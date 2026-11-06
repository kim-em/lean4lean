import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionHistory

/-! # Dependent function types retain carrier histories

The codomain child follows computation and substitution of the domain. At
actual sort-typed endpoints, the carrier children supply the ordinary type
comparisons required by the sorted Pi rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Sorted Pi comparison consumes a hereditary codomain child after independent
core computation of both domains and codomains. -/
theorem PiInertInterpret.forallSorted
    (hs : D.Sound env univs)
    (SA : DomainSort Δ A u) (SC : DomainSort Δ C u)
    (SB : DomainSort (A :: Δ) B v) (SE : DomainSort (A :: Δ) E v)
    (HA : PiInertInterpret D stage (.compare true) Δ A C)
    (HB : PiInertEvidence D stage (.compare true) (A :: Δ) B E) :
    PiInertInterpret D stage (.compare mode) Δ (.forallE A B) (.forallE C E) := by
  intro a' b' RA RB
  obtain ⟨A', B', rfl, RD, RL⟩ := RA.pi_parts (fun R => erased_level_core_no_pi R)
  obtain ⟨C', E', rfl, RC, RR⟩ := RB.pi_parts (fun R => erased_level_core_no_pi R)
  have H' := HB.substitute (ContextSubstitution.core_binder hs RD)
  have SL := ContextSubstitution.sort (ContextSubstitution.core_binder hs RD) (SB.level_core hs RL)
  have SR := ContextSubstitution.sort (ContextSubstitution.core_binder hs RD) (SE.level_core hs RR)
  simp only [ProofShape.subst_id] at H' SL SR
  exact .forallSorted (SA.level_core hs RD) (SC.level_core hs RC) (HA RD RC) SL SR (H'.base RL RR)

/-- The sorted Pi rule retains every future typed substitution at the same
stage, including substitutions exposing new redexes beneath the binder. -/
theorem PiInertEvidence.forallSorted
    (hs : D.Sound env univs)
    (SA : DomainSort Δ A u) (SC : DomainSort Δ C u)
    (SB : DomainSort (A :: Δ) B v) (SE : DomainSort (A :: Δ) E v)
    (HA : PiInertEvidence D stage (.compare true) Δ A C)
    (HB : PiInertEvidence D stage (.compare true) (A :: Δ) B E) :
    PiInertEvidence D stage (.compare mode) Δ (.forallE A B) (.forallE C E) := by
  refine ⟨PiInertInterpret.forallSorted hs SA SC SB SE HA.base HB, ?_⟩
  intro Δ' τ W
  intro left right RL RR
  exact PiInertInterpret.forallSorted hs (W.sort SA) (W.sort SC)
    (ContextSubstitution.sort W.cons SB) (ContextSubstitution.sort W.cons SE) (HA.future W) (HB.substitute W.cons) RL RR

/-- Carrier histories for the domain and codomain construct the actual Pi
congruence case. The right codomain is initially typed in the left domain's
context; reflection of the domain child supplies the required context change.
This does not assume general carrier conversion or strong-derivation coverage. -/
theorem pi_inert_forall_carrier_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hE : env.HasType univs (A :: Γ) E (.sort v))
    (HA : PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.sort u))
      (proofErase Γ A) (proofErase Γ C))
    (HB : PiInertCarrierHistory D stage (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.sort v)) (proofErase (A :: Γ) B) (proofErase (A :: Γ) E)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.sort (.imax u v)))
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HD := HA.evidence.types_checked heq hs hΓ hA hC hA
  have HE := HB.evidence.types_checked heq hs hΓA hB hE hB
  have HAC := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs stage) hΓ hA hC
    (.carrierChecked ((HD.base .refl .refl).mono (fun R => pi_inert_stage_embed R)))
  have W : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hE' := hE.defeqDFC henv W
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (.forallE hA hB)),
    show proofErase Γ (.forallE C E) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (.forallE hC hE'))]
  rw [← proofErase_defeqCtx hΓA W hE]
  exact (PiInertEvidence.forallSorted hs (DomainSort.of_typed hΓ hA)
    (DomainSort.of_typed hΓ hC) (DomainSort.of_typed hΓA hB)
    (DomainSort.of_typed hΓA hE) HD HE).carrier_history

end Lean4Lean.VEnv.Strengthening
