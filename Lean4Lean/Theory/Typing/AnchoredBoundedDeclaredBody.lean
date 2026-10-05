import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredBody
import Lean4Lean.Theory.Typing.AnchoredBoundedCode

/-! The declared native RHS body is aligned at one fixed stage fuel. Only
original natural-lambda formation/conversion children are interpreted, and
the finite Pi certificates used to inspect the telescope keep that fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure InitialNativeAlignment (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (natural assigned : VExpr) (support : Profile n)
    extends Adapted.InitialNativeAlignment env U registry target locals σ available natural assigned support where
  certificateBound : naturalCertificate.nativeDepth current ≤ fuel

inductive OriginalLambdaTypePath (current : Name → Bool) (fuel : Nat) (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source : List VExpr) : VExpr → VExpr → Prop
  | refl : OriginalLambdaTypePath current fuel sourceEnv env U registry source A A
  | tail : OriginalLambdaTypePath current fuel sourceEnv env U registry source A B →
      sourceEnv.IsDefEqStrong U source B C (.sort level) →
      Joint current fuel env U registry source B C (.sort level) →
      OriginalLambdaTypePath current fuel sourceEnv env U registry source A C

/-- The original natural lambda typing, before its outer type conversions.
The body type is stored literally, together with its original-child semantics. -/
structure OriginalLambdaOrigin (current : Name → Bool) (fuel : Nat) (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source : List VExpr) (A body assigned : VExpr) where
  bodyType : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainStrong : sourceEnv.IsDefEqStrong U source A A (.sort domainLevel)
  bodyTypeStrong : sourceEnv.IsDefEqStrong U (A :: source) bodyType bodyType (.sort bodyLevel)
  bodyStrong : sourceEnv.IsDefEqStrong U (A :: source) body body bodyType
  bodyTyping : sourceEnv.HasTypeStrong U (A :: source) body bodyType true
  domainJoint : Joint current fuel env U registry source A A (.sort domainLevel)
  bodyTypeJoint : Joint current fuel env U registry (A :: source) bodyType bodyType (.sort bodyLevel)
  bodyJoint : Joint current fuel env U registry (A :: source) body body bodyType
  naturalJoint : Joint current fuel env U registry source (.forallE A bodyType) (.forallE A bodyType)
    (.sort (.imax domainLevel bodyLevel))
  conversions : OriginalLambdaTypePath current fuel sourceEnv env U registry source (.forallE A bodyType) assigned

/-- Only the original lam children and outer conversion children are sent to
`earlier`, the theorem at the strict predecessor declaration stage. In
particular the declared codomain is never inferred by lambda/Pi inversion. -/
theorem HasTypeStrong.originalLambdaOrigin
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Joint current fuel env U registry Γ left right type)
    {source : List VExpr} {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    {A body : VExpr} (isLambda : expression = .lam A body) :
    Nonempty (OriginalLambdaOrigin current fuel sourceEnv env U registry source A body assigned) := by
  induction original generalizing A body with
  | lam hu hv domain bodyType bodyTyping natural _ _ _ _ =>
    cases isLambda
    exact ⟨{
      bodyType := _
      domainLevel := _
      bodyLevel := _
      domainStrong := domain.refl
      bodyTypeStrong := bodyType.refl
      bodyStrong := bodyTyping.refl
      bodyTyping := bodyTyping
      domainJoint := earlier domain.refl
      bodyTypeJoint := earlier bodyType.refl
      bodyJoint := earlier bodyTyping.refl
      naturalJoint := earlier natural.refl
      conversions := .refl }⟩
  | base _ ih => exact ih isLambda
  | defeq hu conversion _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih isLambda
    exact ⟨{ origin with conversions := .tail origin.conversions conversion (earlier conversion) }⟩
  | _ => cases isLambda

/-- A concrete certificate crosses the retained conversion chain without
changing its finite profile. The returned certificate is still actual source
syntax; the semantic bridge and raw path point back to the natural Pi type. -/
theorem OriginalLambdaTypePath.transfer
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {natural assigned : VExpr}
    (path : OriginalLambdaTypePath current fuel sourceEnv env U registry source natural assigned)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ natural support footprint)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available)
    (selfCode : TypeRelated env U registry target (natural.subst σ) (natural.subst σ) support) :
    Nonempty (InitialNativeAlignment current fuel env U registry target locals σ available natural assigned support) := by
  induction path with
  | refl => exact ⟨⟨⟨footprint, certificate, resources, .refl, selfCode⟩, certificateBound⟩⟩
  | tail _ conversion joint ih =>
    obtain ⟨previous⟩ := ih
    obtain ⟨next⟩ := Transfer.codeCertificate henv hscoped hTarget closed
      (joint target locals σ σ available closed hTarget substitutions fits).1
      previous.naturalCertificate previous.certificateBound previous.resources
    have raw := (conversion.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
    exact ⟨{
      footprint := next.footprint
      naturalCertificate := next.certificate
      resources := next.available
      path := (TypeConversion.single raw).symm.trans previous.path
      related := TypeRelated.trans henv (next.related.symm henv certificate.formed.wf_value)
        previous.related
      certificateBound := next.certificateBound }⟩

/-- The chain starts with the original whole natural-Pi formation child;
there is no separate caller-supplied semantic identity capability. -/
theorem OriginalLambdaOrigin.transport
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A body assigned : VExpr}
    (origin : OriginalLambdaOrigin current fuel sourceEnv env U registry source A body assigned)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (.forallE A origin.bodyType) support footprint)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeAlignment current fuel env U registry target locals σ available
      (.forallE A origin.bodyType) assigned support) := by
  obtain ⟨base⟩ := Transfer.codeCertificate henv hscoped hTarget closed
    (origin.naturalJoint target locals σ σ available closed hTarget substitutions fits).1
    certificate certificateBound resources
  exact origin.conversions.transfer henv hscoped hle closed hTarget substitutions fits
    base.certificate base.certificateBound base.available base.related


private def dropSubst (σ : Subst) (count : Nat) : Subst := fun i => σ (i + count)

private theorem dropSubst_cons (σ : Subst) (count : Nat) :
    dropSubst σ count = (dropSubst σ (count + 1)).cons (σ count) := by
  funext i
  cases i <;> simp [dropSubst, Subst.cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem prefixSubst
    (whole : Ctx.SubstEq env U target σ σ (front ++ source)) :
    Ctx.SubstEq env U target (dropSubst σ front.length) (dropSubst σ front.length) source := by
  induction front generalizing σ with
  | nil =>
    change Ctx.SubstEq env U target σ σ source
    simpa only [List.nil_append] using whole
  | cons A rest ih =>
    cases whole with
    | cons tail _ _ =>
      have equality : dropSubst σ.tail rest.length = dropSubst σ (rest.length + 1) := by
        funext i
        simp only [dropSubst, Subst.tail, Nat.add_assoc]
      have previous := ih tail
      rw [equality] at previous
      exact previous

private theorem emptyCode {profile : Profile n} (h : profile = .empty) :
    TypeRelated env U registry target A B profile := by
  subst profile
  cases n <;> intro Δ ρ future atom member <;> cases member

private theorem emptyRelated :
    Related env U registry target a b A (.empty : Profile n) .empty := by
  cases n <;> intro atom member <;> cases member

private theorem emptyFootprint {footprint : Footprint} (resources : footprint.Available (fun _ => [])) : footprint = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry member
  exact List.not_mem_nil (resources entry.1 entry.2 member)

/-- The continuation is constructed by finite syntax recursion. Its inputs
are concrete code/path evidence, not source-typing or adequacy callbacks. -/
private structure DeclaredBodyPlan (current : Name → Bool) (fuel : Nat) (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (locals : List Nat) (σ : Subst) (domains : List VExpr) (body assigned : VExpr) where
  bodyType : VExpr
  originalBody : sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body bodyType
  bodyJoint : Joint current fuel env U registry (domains.reverse ++ source) body body bodyType
  rank : Nat
  profile : Profile rank
  certificate : CodeCert env U registry target locals (dropSubst σ domains.length) assigned profile []
  certificateBound : certificate.nativeDepth current ≤ fuel
  decode : ∀ result,
    TypeConversion env U target (assigned.subst (dropSubst σ domains.length))
      ((wrapForalls domains result).subst (dropSubst σ domains.length)) →
    TypeRelated env U registry target (assigned.subst (dropSubst σ domains.length))
      ((wrapForalls domains result).subst (dropSubst σ domains.length)) profile →
    TypeConversion env U target (bodyType.subst σ) (result.subst σ)

private theorem declaredBodyPlan
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Joint current fuel env U registry Γ left right type)
    (domains : List VExpr) {source target : List VExpr} {body assigned : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body) assigned structural)
    (locals : List Nat) (σ : Subst) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (domains.reverse ++ source)) :
    Nonempty (DeclaredBodyPlan current fuel sourceEnv env U registry target source locals σ domains body assigned) := by
  induction domains generalizing source assigned structural locals with
  | nil =>
    exact ⟨{
      bodyType := assigned
      originalBody := original.refl
      bodyJoint := earlier original.refl
      rank := 0
      profile := .empty
      certificate := .seed .empty (.empty (.sort true))
      certificateBound := by simp only [CodeCert.nativeDepth, Obs.nativeDepth]; omega
      decode := fun result path _ => by
        change TypeConversion env U target (assigned.subst σ) (result.subst σ) at path
        exact path }⟩
  | cons A domains ih =>
    obtain ⟨origin⟩ := HasTypeStrong.originalLambdaOrigin earlier original rfl
    have innerSubst : Ctx.SubstEq env U target σ σ (domains.reverse ++ A :: source) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using substitutions
    obtain ⟨inner⟩ := ih origin.bodyTyping (Locals.push locals) innerSubst
    let base := dropSubst σ (domains.length + 1)
    let argument := σ domains.length
    have atBinder := prefixSubst (front := domains.reverse) innerSubst
    have atBinderCons : Ctx.SubstEq env U target (base.cons argument) (base.cons argument) (A :: source) := by
      rw [List.length_reverse, dropSubst_cons σ domains.length] at atBinder
      exact atBinder
    have hBase : Ctx.SubstEq env U target base base source := by
      cases atBinderCons with
      | cons previous _ _ => simpa only [Subst.cons_tail] using previous
    have argumentTyped : env.HasType U target argument (A.subst base) := by
      cases atBinderCons with
      | cons _ _ value => simpa only [HasType, Subst.cons_tail, Subst.head, Subst.cons] using value
    let key : Key inner.rank := ⟨A.subst base, argument, .empty⟩
    have admitted : Admitted env U registry target key argument argument :=
      ⟨argumentTyped, argumentTyped, .empty, .empty .empty, .empty (.sort true),
        emptyCode rfl, emptyRelated, emptyRelated⟩
    have guard : LambdaGuard env U registry target base A key .empty :=
      ⟨.empty .empty, .empty (.sort true), .refl, emptyCode rfl, admitted⟩
    have childData : ∃ child : CodeCert env U registry target (Locals.push locals) (base.cons argument)
        origin.bodyType inner.profile [], child.nativeDepth current ≤ fuel := by
      have child : ∃ c : CodeCert env U registry target (Locals.push locals)
          (dropSubst σ domains.length) origin.bodyType inner.profile [], c.nativeDepth current ≤ fuel :=
        ⟨inner.certificate, inner.certificateBound⟩
      rw [dropSubst_cons σ domains.length] at child
      exact child
    obtain ⟨childCertificate, childBound⟩ := childData
    let profile : Profile (inner.rank + 1) :=
      .pi (A.subst base) (origin.bodyType.subst base.lift) .empty [(key, inner.profile)]
    have formed : profile.HasType (.sort true) := by
      apply Profile.HasType.pi_iff.mpr
      refine ⟨Profile.WF.pi_iff.mpr ⟨.empty (.sort true), ?_⟩, ?_⟩
      · intro k output member
        cases List.mem_singleton.mp member
        exact ⟨.empty .empty, childCertificate.formed.wf_value⟩
      · intro k output member
        cases List.mem_singleton.mp member
        exact childCertificate.formed
    let naturalCertificate : CodeCert env U registry target locals base
        (.forallE A origin.bodyType) profile [] :=
      .seed (.pi (.seed .empty (.empty (.sort true))) PiGuard.literal
        (.cons guard childCertificate .nil (fun _ h => nomatch h) .nil)) formed
    have naturalBound : naturalCertificate.nativeDepth current ≤ fuel := by
      simpa only [naturalCertificate, CodeCert.nativeDepth, Obs.nativeDepth, PiRows.nativeDepth, Nat.max_zero, Nat.zero_max] using childBound
    have fits : PairedFits current fuel env U registry source target locals base base (fun _ => []) := by
      constructor <;> constructor <;> intro _ _ member <;> cases member
    have closed : Valuation.AtomClosed (fun _ => []) := by
      intro _ _ member; cases member
    obtain ⟨aligned⟩ := origin.transport henv hscoped hle closed hTarget hBase fits
      naturalCertificate naturalBound (fun _ _ h => nomatch h)
    have noFootprint := emptyFootprint aligned.resources
    have finalCertificate : ∃ c : CodeCert env U registry target locals
        (dropSubst σ (A :: domains).length) assigned profile [], c.nativeDepth current ≤ fuel := by
      have witness : ∃ c : CodeCert env U registry target locals base assigned profile aligned.footprint,
          c.nativeDepth current ≤ fuel := ⟨aligned.naturalCertificate, aligned.certificateBound⟩
      rw [noFootprint] at witness
      exact witness
    obtain ⟨certificate, certificateBound⟩ := finalCertificate
    refine ⟨{
      bodyType := inner.bodyType
      originalBody := ?_
      bodyJoint := ?_
      rank := inner.rank + 1
      profile := profile
      certificate := certificate
      certificateBound := certificateBound
      decode := ?_ }⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using inner.originalBody
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using inner.bodyJoint
    · intro result _ incoming
      have forward := aligned.related.symm henv formed.wf_value
      have full := TypeRelated.trans henv forward incoming
      change TypeRelated env U registry target
        (.forallE (A.subst base) (origin.bodyType.subst base.lift))
        (.forallE (A.subst base) ((wrapForalls domains result).subst base.lift)) profile at full
      have child := full.literalPiBody henv hscoped hTarget (List.mem_singleton_self _) admitted
      have path : TypeConversion env U target (origin.bodyType.subst (dropSubst σ domains.length))
          ((wrapForalls domains result).subst (dropSubst σ domains.length)) := by
        simpa only [inst_lift_cons, base, argument, ← dropSubst_cons] using child.1
      have code : TypeRelated env U registry target (origin.bodyType.subst (dropSubst σ domains.length))
          ((wrapForalls domains result).subst (dropSubst σ domains.length)) inner.profile := by
        simpa only [inst_lift_cons, base, argument, ← dropSubst_cons] using child.2
      exact inner.decode result path code


/-- Open the exact declared equation telescope at a concrete typed capture
substitution. The natural terminal typing and its semantics come from original
children; the exact declared result typing follows from a constructed raw path.
The only semantic theorem parameter is the strict predecessor-stage theorem. -/
theorem HasTypeStrong.declaredBody
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Joint current fuel env U registry Γ left right type)
    {source target : List VExpr} {domains : List VExpr} {body result : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (σ : Subst) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (domains.reverse ++ source)) :
    ∃ natural,
      sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body natural ∧
      Joint current fuel env U registry (domains.reverse ++ source) body body natural ∧
      TypeConversion env U target (natural.subst σ) (result.subst σ) ∧
      env.HasType U target (body.subst σ) (result.subst σ) := by
  obtain ⟨plan⟩ := declaredBodyPlan henv hscoped hle earlier domains original [] σ hTarget substitutions
  have baseSubst : Ctx.SubstEq env U target (dropSubst σ domains.length)
      (dropSubst σ domains.length) source := by
    simpa only [List.length_reverse] using prefixSubst (front := domains.reverse) substitutions
  have fits : PairedFits current fuel env U registry source target [] (dropSubst σ domains.length)
      (dropSubst σ domains.length) (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ member <;> cases member
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro _ _ member; cases member
  obtain ⟨typedCode⟩ := Transfer.codeCertificate henv hscoped hTarget closed
    (earlier formation target [] _ _ _ closed hTarget baseSubst fits).1
    plan.certificate plan.certificateBound (fun _ _ h => nomatch h)
  have path := plan.decode result .refl typedCode.related
  have raw := (plan.originalBody.defeq.mono hle).subst henv substitutions hTarget
  exact ⟨plan.bodyType, plan.originalBody, plan.bodyJoint, path, path.cast raw⟩

/-- Literal open-body specialization: the returned typing is at the declared
result itself, not only at its substitution by a particular capture tuple. -/
theorem HasTypeStrong.openDeclaredBody
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Joint current fuel env U registry Γ left right type)
    {source : List VExpr} {domains : List VExpr} {body result : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (hContext : OnCtx (domains.reverse ++ source) (env.IsType U)) :
    ∃ natural,
      sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body natural ∧
      Joint current fuel env U registry (domains.reverse ++ source) body body natural ∧
      TypeConversion env U (domains.reverse ++ source) natural result ∧
      env.HasType U (domains.reverse ++ source) body result := by
  simpa only [subst_id] using HasTypeStrong.declaredBody henv hscoped hle earlier original
    formation Subst.id hContext (Ctx.SubstEq.id henv hContext)


end Lean4Lean.AnchoredSource.Adapted.Staged
