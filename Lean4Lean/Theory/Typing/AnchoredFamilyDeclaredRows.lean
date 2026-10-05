import Lean4Lean.Theory.Typing.AnchoredFamilyCodePath
import Lean4Lean.Theory.Typing.AnchoredFamilySeededAlignment

/-! Forward recovery of actual declared family rows from the backwards source
request. A finite row history bridges the snoc source application path and the
cons dependent telescope. Every full argument input remains in the ledger.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

inductive FamilyRowHistory (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (source₀ : List VExpr) (locals₀ : List Nat) (seed₀ : Subst)
    (available₀ : Valuation) (expression₀ : VExpr) :
    List VExpr → List Nat → Subst → Valuation → VExpr →
      List VExpr → List FamilyKey → Type where
  | nil : FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
      expression₀ source₀ locals₀ seed₀ available₀ expression₀ [] []
  | snoc
      (history : FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
        expression₀ source locals seed available (.forallE A B) domains keys)
      (original : OriginalTypePayload sourceEnv env U registry source A (.sort level))
      (row : PiRowCertificate env U registry target locals seed available A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra) :
      FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
        expression₀ (A :: source) (Locals.push locals) (seed.cons key.anchor)
        (Valuation.push (row.seedNeeds extra) available) B
        (domains ++ [A]) (keys ++ [⟨n, key, support⟩])

/-- Close the finite forward history with the actual remaining rows. This
operation stores no semantic callback and makes no new source observation. -/
theorem FamilyRowHistory.close
    (history : FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
      expression₀ source locals seed available expression domains keys)
    (tail : FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
      expression remaining remainingKeys) :
    Nonempty (FamilySeededCodeRows sourceEnv env U registry target required source₀ locals₀ seed₀ available₀
      expression₀ (domains ++ remaining) (keys ++ remainingKeys)) := by
  induction history generalizing remaining remainingKeys with
  | nil => exact ⟨tail⟩
  | snoc history original row admission extra bounded covered inputPresent ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (FamilySeededCodeRows.cons original row admission extra bounded covered inputPresent tail)

theorem FamilyRowHistory.closeExact
    (history : FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
      expression₀ source locals seed available expression domains keys)
    (tail : FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
      expression remaining remainingKeys) :
    ∃ rows : FamilySeededCodeRows sourceEnv env U registry target required source₀ locals₀ seed₀ available₀
        expression₀ (domains ++ remaining) (keys ++ remainingKeys),
      rows.terminalLocals = tail.terminalLocals ∧ rows.terminalValuation = tail.terminalValuation := by
  induction history generalizing remaining remainingKeys with
  | nil => exact ⟨tail, rfl, rfl⟩
  | snoc history original row admission extra bounded covered inputPresent ih =>
    rw [List.append_assoc, List.singleton_append, List.append_assoc, List.singleton_append]
    exact ih (FamilySeededCodeRows.cons original row admission extra bounded covered inputPresent tail)

theorem FamilyRowHistory.seed_eq
    (history : FamilyRowHistory sourceEnv env U registry target source₀ locals₀ seed₀ available₀
      expression₀ source locals seed available expression domains keys) :
    familySubst seed₀ (keys.map (·.key.anchor)) = seed := by
  induction history with
  | nil => rfl
  | snoc history original row admission extra bounded covered inputPresent ih =>
    simp only [List.map_append, List.map_singleton, familySubst, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

structure FamilyDeclaredCodePrefix (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (signature : ConstantTelescope declaredType)
    (arguments : List VExpr) (support : Profile n) (keys : List FamilyKey)
    extends ConstantCodePrefix env U registry target locals σ available signature arguments support where
  history : FamilyRowHistory sourceEnv env U registry target [] [] (nativeCaptureSubst [])
    (fun _ => []) declaredType (signature.domains.take arguments.length).reverse
    (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
    (wrapForalls (signature.domains.drop arguments.length) signature.result)
    (signature.domains.take arguments.length) keys

/-- Read every selected row from the actual declared header certificate.
The current frame's complete finite input is kept as an explicit seed need,
so later field certificates can use the requests that built the header. -/
theorem FamilyCodePath.atDeclaredFamily
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {signature : ConstantTelescope declaredType}
    (formation : OriginalTypePayload sourceEnv env U registry [] declaredType (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] declaredType)
    {arguments : List VExpr} {profile : Profile n} {root : Profile N}
    (path : FamilyCodePath env U registry target locals σ available arguments profile root)
    (bound : arguments.length ≤ signature.domains.length)
    (initial : FamilyDeclaredCodePrefix sourceEnv env U registry target locals σ available
      signature [] root []) :
    Nonempty (FamilyDeclaredCodePrefix sourceEnv env U registry target locals σ available
      signature arguments profile path.keys) := by
  induction path with
  | nil => exact ⟨initial⟩
  | @snoc A B a n result before request args N root frame prior ih =>
    have beforeBound : args.length < signature.domains.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    obtain ⟨previous⟩ := ih (by omega) initial
    have origin : signature.domains[args.length]? = some signature.domains[args.length] :=
      List.getElem?_eq_getElem beforeBound
    have literal := signature.prefixResidual_cons origin
    have tree := (signature.prefixPayload ⟨level, formation⟩ header args.length).1.2
    have certificate := previous.certificate
    have history := previous.history
    rw [literal] at tree certificate history
    obtain ⟨domainLevel, rawDomain, originalDomain⟩ := tree.domain.1
    obtain ⟨bodyLevel, rawBody, originalBody⟩ := tree.codomain.1
    have origins := certificate.piOrigins henv hscoped hTarget previous.closed
      (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) previous.substitutions previous.fits
      originalDomain originalBody previous.resources
    obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key
      (raiseProfile frame.rank frame.outputBound result) (List.mem_singleton_self _)
    let extra : List Need := [⟨frame.rank, frame.input⟩]
    have extraBound : ∀ need ∈ extra, need.rank ≤ frame.rank := by
      intro need member
      cases List.mem_singleton.mp member
      exact Nat.le_refl _
    have extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade frame.rank).atoms,
        atom ∈ frame.key.input.atoms := by
      intro need member
      cases List.mem_singleton.mp member
      simpa only [Need.atGrade, dif_pos (Nat.le_refl _), raiseProfile_self, FamilyApplicationInput.key] using
        (fun atom (member : atom ∈ frame.input.atoms) => member)
    have inputPresent : (⟨frame.rank, frame.key.input⟩ : Need) ∈ row.seedNeeds extra :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨raw, localFits⟩ := row.pushSeed henv hscoped hle ⟨rawDomain, originalDomain⟩
      previous.closed hTarget previous.substitutions previous.fits extra extraBound extraCovered
    have coverage := row.seedCoverage extra extraBound extraCovered
    have localObserved := previous.observed.push closed frame.argumentObservation frame.argumentAvailable
      (fun need member => (coverage need member).1) (fun need member => (coverage need member).2)
    have contextEq := signature.prefixContext_cons origin
    have localsEq : List.range (args ++ [a]).length = Locals.push (List.range args.length) := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have lengthEq : (args ++ [a]).length = args.length + 1 := by simp
    have realized : nativeCaptureSubst ((args ++ [a]).map (·.subst σ)) =
        (nativeCaptureSubst (args.map (·.subst σ))).cons frame.key.anchor := by
      rw [List.map_append, List.map_singleton, nativeCaptureSubst_append]
      rfl
    have taken : signature.domains.take (args.length + 1) =
        signature.domains.take args.length ++ [signature.domains[args.length]] := by
      rw [List.take_add_one, origin]
      rfl
    refine ⟨{
      valuation := Valuation.push (row.seedNeeds extra) previous.valuation
      closed := row.seedClosed extra previous.closed
      substitutions := ?_
      fits := ?_
      footprint := row.bodyFootprint
      certificate := ?_
      resources := row.seedBodyAvailable extra
      observed := localObserved
      history := ?_ }⟩
    · simpa only [lengthEq, contextEq, realized] using raw
    · simpa only [lengthEq, contextEq, realized, localsEq, List.range_succ_eq_map, Locals.push] using localFits
    · simpa only [lengthEq, realized, localsEq, List.range_succ_eq_map, Locals.push] using
        row.body.lowerRaised frame.outputBound
    · simpa only [lengthEq, contextEq, realized, localsEq, taken, FamilyCodePath.keys,
        List.range_succ_eq_map, Locals.push, List.reverse_append, List.reverse_singleton,
        List.singleton_append] using
        FamilyRowHistory.snoc history ⟨rawDomain, originalDomain⟩ row (frame.guard.familyAdmission henv) extra extraBound extraCovered inputPresent

/-- Start from the actual constant lookup and close the source footprint
using the original header's syntactic closedness. -/
theorem FamilyCodeRoot.atDeclaredFamily
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
    (root : FamilyCodeRoot sourceEnv env U registry target locals σ available name levels arguments profile)
    (bound : arguments.length ≤ signature.domains.length) :
    Nonempty (FamilyDeclaredCodePrefix sourceEnv env U registry target locals σ available signature
      arguments profile root.path.keys) := by
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
  apply root.path.atDeclaredFamily henv hscoped hle closed hTarget formation header bound
  exact {
    valuation := fun _ => []
    closed := by intro _ _ h; cases h
    substitutions := .nil
    fits := .nil
    footprint := []
    certificate := certificate
    resources := by intro _ _ h; cases h
    observed := NativeObservedValuation.empty
    history := by simpa only [List.length_nil, List.take_zero, List.reverse_nil,
      List.range_zero, List.map_nil, List.drop_zero, signature.type_eq] using
      (FamilyRowHistory.nil (sourceEnv := sourceEnv) (env := env) (U := U) (registry := registry)
        (target := target) (source₀ := []) (locals₀ := []) (seed₀ := nativeCaptureSubst [])
        (available₀ := fun _ => []) (expression₀ := info.type.instL levels)) }

/-- The completed forward history produces the actual finite declared row
packet. Only the requested terminal footprint's availability is needed to
close it; all source rows were constructed from original header certificates. -/
theorem FamilyDeclaredCodePrefix.rows
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (declared : FamilyDeclaredCodePrefix sourceEnv env U registry target locals σ available
      signature arguments profile keys)
    (saturated : arguments.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel)
    (resources : required.Available declared.valuation) :
    Nonempty (FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys) := by
  have history := declared.history
  simp only [saturated, List.take_length, List.drop_length, wrapForalls, resultSort] at history
  simpa only [List.append_nil] using history.close (FamilySeededCodeRows.nil resources)

/-- Public source producer. It starts with the ORIGINAL possibly converted
family/constructor application typing and a finite list of actual argument
observations. The result stores declared rows and their finite strict grade
bound, ready for the binary family-code alignment consumer. -/
theorem HasTypeStrong.familyDeclaredPrefix
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
    (requests : FamilyArgumentRequests env U registry target locals σ available expression.getAppFnArgs.2)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    ∃ rank keys, (∀ key ∈ keys, key.rank < rank) ∧
      Nonempty (FamilyDeclaredCodePrefix sourceEnv env U registry target locals σ available signature
        expression.getAppFnArgs.2 profile keys) := by
  obtain ⟨spine⟩ := HasTypeStrong.familySpineCertificate henv hscoped hle earlier closed hTarget
    substitutions fits original head requests certificate resources
  let root := spine.codeRoot
  have payload := earlier formation
  refine ⟨root.rank, root.path.keys, fun key member => root.path.keyBound member, ?_⟩
  exact root.atDeclaredFamily henv hscoped hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation bound

end Lean4Lean.AnchoredSource.Adapted
