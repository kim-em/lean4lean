import Lean4Lean.Theory.Typing.AnchoredConstantTelescope
import Lean4Lean.Theory.Typing.AnchoredNativeCodePath
import Lean4Lean.Theory.Typing.AnchoredNativeCodeRow
import Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan

/-! Original constant-spine provenance for an arbitrary declared telescope.
Family and constructor headers use the same actual source cuts as native
headers; no recursor metadata or raw type injectivity is required. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false



structure ConstantCodePrefix (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (signature : ConstantTelescope declaredType)
    (arguments : List VExpr) (support : Profile n) where
  valuation : Valuation
  closed : valuation.AtomClosed
  substitutions : Ctx.SubstEq env U target
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (signature.domains.take arguments.length).reverse
  fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
    (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.subst σ)))
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
  footprint : Footprint
  certificate : CodeCert env U registry target (List.range arguments.length)
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (wrapForalls (signature.domains.drop arguments.length) signature.result) support footprint
  resources : footprint.Available valuation
  observed : NativeObservedValuation env U registry target locals σ available arguments valuation

theorem NativeCodePath.atConstantTelescope
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {signature : ConstantTelescope declaredType}
    (formation : OriginalTypePayload sourceEnv env U registry [] declaredType (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] declaredType)
    {arguments : List VExpr} {profile : Profile n} {root : Profile N}
    (path : NativeCodePath env U registry target locals σ available arguments profile root)
    (bound : arguments.length ≤ signature.domains.length)
    (initial : ConstantCodePrefix env U registry target locals σ available signature [] root) :
    Nonempty (ConstantCodePrefix env U registry target locals σ available signature arguments profile) := by
  induction path with
  | nil => exact ⟨initial⟩
  | @snoc A B a n result before args N root frame prior ih =>
    have beforeBound : args.length < signature.domains.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    obtain ⟨previous⟩ := ih (by omega) initial
    have origin : signature.domains[args.length]? = some signature.domains[args.length] :=
      List.getElem?_eq_getElem beforeBound
    have literal := signature.prefixResidual_cons origin
    have tree := (signature.prefixPayload ⟨level, formation⟩ header args.length).1.2
    have certificate := previous.certificate
    rw [literal] at tree certificate
    obtain ⟨domainLevel, rawDomain, originalDomain⟩ := tree.domain.1
    obtain ⟨bodyLevel, rawBody, originalBody⟩ := tree.codomain.1
    have origins := certificate.piOrigins henv hscoped hTarget previous.closed
      (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) previous.substitutions previous.fits
      originalDomain originalBody previous.resources
    obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key
      (raiseProfile frame.input.rank frame.input.bound result) (List.mem_singleton_self _)
    obtain ⟨raw, localFits, bodyAvailable⟩ := row.pushCode henv hscoped hle
      ⟨rawDomain, originalDomain⟩ previous.closed hTarget previous.substitutions previous.fits
    have localObserved := previous.observed.push closed frame.input.observation frame.input.argumentAvailable
      (fun need member => (row.codeCoverage need member).1)
      (fun need member => (row.codeCoverage need member).2)
    have contextEq := signature.prefixContext_cons origin
    have localsEq : List.range (args ++ [a]).length = Locals.push (List.range args.length) := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have lengthEq : (args ++ [a]).length = args.length + 1 := by simp
    have realized : nativeCaptureSubst ((args ++ [a]).map (·.subst σ)) =
        (nativeCaptureSubst (args.map (·.subst σ))).cons frame.key.anchor := by
      rw [List.map_append, List.map_singleton, nativeCaptureSubst_append]
      rfl
    refine ⟨{
      valuation := Valuation.push row.codeNeeds previous.valuation
      closed := row.codeClosed previous.closed
      substitutions := ?_
      fits := ?_
      footprint := row.bodyFootprint
      certificate := ?_
      resources := bodyAvailable
      observed := localObserved }⟩
    · simpa only [lengthEq, contextEq, realized] using raw
    · simpa only [lengthEq, contextEq, realized, localsEq, List.range_succ_eq_map, Locals.push] using localFits
    · simpa only [lengthEq, realized, localsEq, List.range_succ_eq_map, Locals.push] using
        row.body.lowerRaised frame.input.bound

/-- Start at the actual constant lookup and its original closed formation
child. All argument-domain certificates are then produced from the retained
source path, including paths whose final requested output is empty. -/
theorem NativeCodeRoot.atConstantTelescope
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (typeClosed : (info.type.instL levels).Closed)
    (formation : OriginalTypePayload sourceEnv env U registry [] (info.type.instL levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] (info.type.instL levels))
    {arguments : List VExpr} {profile : Profile n}
    (root : NativeCodeRoot sourceEnv env U registry target locals σ available name levels arguments profile)
    (bound : arguments.length ≤ signature.domains.length) :
    Nonempty (ConstantCodePrefix env U registry target locals σ available signature arguments profile) := by
  have infoEq : root.info = info := Option.some.inj (root.lookup.symm.trans lookup)
  have footprintEmpty : root.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    have scope : (root.info.type.instL levels).Closed := by rw [infoEq]; exact typeClosed
    have impossible := root.certificate.scoped scope index need member
    omega
  have certificate : CodeCert env U registry target [] (nativeCaptureSubst [])
      (wrapForalls signature.domains signature.result) root.support [] := by
    have actual : CodeCert env U registry target locals σ (info.type.instL levels) root.support [] := by
      rw [← infoEq, ← footprintEmpty]
      exact root.certificate
    rw [← signature.type_eq]
    exact actual.closedSource typeClosed [] (nativeCaptureSubst [])
  apply root.path.atConstantTelescope henv hscoped hle closed hTarget formation header bound
  exact {
    valuation := fun _ => []
    closed := by intro _ _ h; cases h
    substitutions := .nil
    fits := .nil
    footprint := []
    certificate := certificate
    resources := by intro _ _ h; cases h
    observed := NativeObservedValuation.empty }

/-- The public producer starts from the original possibly converted term
typing. A family or constructor consumer provides its concrete declared
telescope, not a proposed argument alignment or a prebuilt source path. -/
theorem HasTypeStrong.constantCodePrefix
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels)
      (info.type.instL levels) (.sort level))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    Nonempty (ConstantCodePrefix env U registry target locals σ available signature
      expression.getAppFnArgs.2 profile) := by
  obtain ⟨spine⟩ := HasTypeStrong.spineCertificate henv hscoped hle earlier closed hTarget
    substitutions fits original head certificate resources
  have payload := earlier formation
  exact spine.codeRoot.atConstantTelescope henv hscoped hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation bound

end Lean4Lean.AnchoredSource.Adapted
