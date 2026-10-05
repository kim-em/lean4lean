import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedLambdaRaw

/-! Actual Pi code from original domain/codomain children and finite source
row certificates. This does not require a computational body induction. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem admitted_right (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : Admitted env U registry Γ key x y) : Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩

theorem CodeCert.piTypeCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B : VExpr} {key : Key n}
    {domainSupport resultSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (body : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
      B resultSupport bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    TypeRelated env U registry target ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst σ)
      (Profile.pi (A.subst σ) (B.subst σ.lift) domainSupport [(key, resultSupport)]) := by
  have rawA := formedA.subst henv substitutions.left hTarget
  have hA : env.IsType U target (A.subst σ) := ⟨_, rawA⟩
  have contextA : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨hTarget, hA⟩
  have rawB := formedB.subst henv (substitutions.left.lift henv formedA) contextA
  have hB : env.IsType U (A.subst σ :: target) (B.subst σ.lift) := ⟨_, rawB⟩
  apply TypeRelated.literalPi henv hA hB guard.inputTyped guard.formed guard.path guard.domains
  intro Δ ρ insertion x y admitted
  have hΔ := insertion.targetWF henv
  have substitutions' := substitutions.future henv insertion
  have fits' := fits.future henv insertion
  have guard' := guard.future henv insertion
  have domain' := domain.future henv insertion
  have body' := body.future henv insertion
  simp only [subst_cons_future] at body'
  have pack' := pack.rename ρ
  have covered' : ∀ atom ∈ (packed.rename ρ).atoms, atom ∈ (key.input.rename ρ).atoms := by
    intro atom hm
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map_of_mem (covered original horiginal)
  let needs := (Footprint.rename ρ bodyFootprint).localNeeds ++
    (Footprint.rename ρ bodyFootprint).localNeeds.flatMap Need.singletons
  have domainChild : GradedTransfer env U registry Δ locals (σ.lift_r ρ) (σ.lift_r ρ)
      (available.rename ρ) A A (.sort domainLevel) :=
    (originalDomain Δ locals _ _ _ (closed.rename ρ) hΔ substitutions' fits').1
  have atArgument : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
      TypeRelated env U registry Δ
        (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
        (B.subst ((σ.lift_r ρ).cons z)) (resultSupport.rename ρ) := by
    intro z hz
    obtain ⟨raw, _, _, _, _, _, first, _⟩ := hz
    have arguments := Related.convert henv guard'.inputTyped guard'.domains first
    have paired : Ctx.SubstEq env U Δ ((σ.lift_r ρ).cons (key.anchor.lift' ρ))
        ((σ.lift_r ρ).cons z) (A :: source) :=
      .cons substitutions' formedA (guard'.path.cast raw)
    have localFits := fits'.pushGraded henv hscoped hΔ (closed.rename ρ) domainChild
      domain' (domainAvailable.rename ρ) guard'.inputTyped arguments needs
      (fun need hm => (pack'.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered' atom ((pack'.atomized_localNeeds need hm).2 atom ha))
    have child : GradedTransfer env U registry Δ (Locals.push locals)
        ((σ.lift_r ρ).cons (key.anchor.lift' ρ)) ((σ.lift_r ρ).cons z)
        (Valuation.push needs (available.rename ρ)) B B (.sort bodyLevel) :=
      (originalCodomain Δ (Locals.push locals) _ _ _
        (Valuation.push_atomized_closed (closed.rename ρ) _) hΔ paired localFits).1
    obtain ⟨transferred⟩ := body'.transfer_graded henv hscoped hΔ
      (Valuation.push_atomized_closed (closed.rename ρ) _) child
      (pack'.available_atomized_localNeeds (outsideAvailable.rename ρ))
    exact transferred.related
  have hx := atArgument x admitted.left_diagonal
  have hy := atArgument y (admitted_right henv hscoped admitted)
  have result := (hx.symm henv body'.formed.wf_value).trans henv hy
  simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using result

end Lean4Lean.AnchoredSource.Adapted
