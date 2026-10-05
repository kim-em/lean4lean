import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment

/-! Exact open declared-body conversion for an original equation telescope.
A finite code certificate is built bottom-up from the original lambda spine;
its literal Pi rows are then read top-down. Only the strict predecessor-stage
theorem interprets original typing/conversion children. No newly cast body
typing becomes a semantic induction argument.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

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
private structure DeclaredBodyPlan (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (locals : List Nat) (σ : Subst) (domains : List VExpr) (body assigned : VExpr) where
  bodyType : VExpr
  originalBody : sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body bodyType
  bodyJoint : GradedJoint env U registry (domains.reverse ++ source) body body bodyType
  rank : Nat
  profile : Profile rank
  certificate : CodeCert env U registry target locals (dropSubst σ domains.length) assigned profile []
  decode : ∀ result,
    TypeConversion env U target (assigned.subst (dropSubst σ domains.length))
      ((wrapForalls domains result).subst (dropSubst σ domains.length)) →
    TypeRelated env U registry target (assigned.subst (dropSubst σ domains.length))
      ((wrapForalls domains result).subst (dropSubst σ domains.length)) profile →
    TypeConversion env U target (bodyType.subst σ) (result.subst σ)

private theorem declaredBodyPlan
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    (domains : List VExpr) {source target : List VExpr} {body assigned : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body) assigned structural)
    (locals : List Nat) (σ : Subst) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (domains.reverse ++ source)) :
    Nonempty (DeclaredBodyPlan sourceEnv env U registry target source locals σ domains body assigned) := by
  induction domains generalizing source assigned structural locals with
  | nil =>
    exact ⟨{
      bodyType := assigned
      originalBody := original.refl
      bodyJoint := earlier original.refl
      rank := 0
      profile := .empty
      certificate := .seed .empty (.empty (.sort true))
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
    have childCertificate : CodeCert env U registry target (Locals.push locals) (base.cons argument)
        origin.bodyType inner.profile [] := by
      have child := inner.certificate
      rw [dropSubst_cons σ domains.length] at child
      exact child
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
    have fits : PairedFits env U registry source target locals base base (fun _ => []) := by
      constructor <;> constructor <;> intro _ _ member <;> cases member
    have closed : Valuation.AtomClosed (fun _ => []) := by
      intro _ _ member; cases member
    obtain ⟨aligned⟩ := origin.transport henv hscoped hle closed hTarget hBase fits
      naturalCertificate (fun _ _ h => nomatch h)
    have noFootprint := emptyFootprint aligned.resources
    refine ⟨{
      bodyType := inner.bodyType
      originalBody := ?_
      bodyJoint := ?_
      rank := inner.rank + 1
      profile := profile
      certificate := ?_
      decode := ?_ }⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using inner.originalBody
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using inner.bodyJoint
    · simpa only [noFootprint, List.length_cons] using aligned.naturalCertificate
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
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source target : List VExpr} {domains : List VExpr} {body result : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (σ : Subst) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (domains.reverse ++ source)) :
    ∃ natural,
      sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body natural ∧
      GradedJoint env U registry (domains.reverse ++ source) body body natural ∧
      TypeConversion env U target (natural.subst σ) (result.subst σ) ∧
      env.HasType U target (body.subst σ) (result.subst σ) := by
  obtain ⟨plan⟩ := declaredBodyPlan henv hscoped hle earlier domains original [] σ hTarget substitutions
  have baseSubst : Ctx.SubstEq env U target (dropSubst σ domains.length)
      (dropSubst σ domains.length) source := by
    simpa only [List.length_reverse] using prefixSubst (front := domains.reverse) substitutions
  have fits : PairedFits env U registry source target [] (dropSubst σ domains.length)
      (dropSubst σ domains.length) (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ member <;> cases member
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro _ _ member; cases member
  obtain ⟨typedCode⟩ := plan.certificate.transfer_graded henv hscoped hTarget closed
    (earlier formation target [] _ _ _ closed hTarget baseSubst fits).1
    (fun _ _ h => nomatch h)
  have path := plan.decode result .refl typedCode.related
  have raw := (plan.originalBody.defeq.mono hle).subst henv substitutions hTarget
  exact ⟨plan.bodyType, plan.originalBody, plan.bodyJoint, path, path.cast raw⟩

/-- Literal open-body specialization: the returned typing is at the declared
result itself, not only at its substitution by a particular capture tuple. -/
theorem HasTypeStrong.openDeclaredBody
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source : List VExpr} {domains : List VExpr} {body result : VExpr}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (hContext : OnCtx (domains.reverse ++ source) (env.IsType U)) :
    ∃ natural,
      sourceEnv.IsDefEqStrong U (domains.reverse ++ source) body body natural ∧
      GradedJoint env U registry (domains.reverse ++ source) body body natural ∧
      TypeConversion env U (domains.reverse ++ source) natural result ∧
      env.HasType U (domains.reverse ++ source) body result := by
  simpa only [subst_id] using HasTypeStrong.declaredBody henv hscoped hle earlier original
    formation Subst.id hContext (Ctx.SubstEq.id henv hContext)

end Lean4Lean.AnchoredSource.Adapted
