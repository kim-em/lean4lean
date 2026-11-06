import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveCastConsumer

/-! # Retaining recursive computation joins through typed consumers

The common raw argument output is realized using certified replay. Both sides
then compute through an arbitrary typed consumer to one actual instantiated
body. No confluence of recursive cast computation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Replay of a recursive computation constructs an actual equal term with
exactly its output erasure. This uses source typing and the proved certified
interpretation, with no separate target recovery premise. -/
theorem RecursiveCastCompute.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ proofErase Γ e' = out :=
  proofErase_scoped_compute_realize (erased_beta_stable_joint_descent heq hs)
    hΓ ht rfl rfl (R.certified heq hs hregistry)

/-- Two recursive paths to the same raw output reflect an actual equality.
The output is realized on the left; uniqueness of typed erasure identifies
the two realizations without any computation-confluence assumption. -/
theorem RecursiveCastCompute.join_defeq
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ b) shared) :
    env.IsDefEq univs Γ a b T :=
  proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ ha hb
    (.carrierChecked (RA.join_family heq hs hregistry hΓ ha hb RB).base)

/-- An explicit argument join propagates through any typed consumer. The
result keeps two recursive paths to an actual common instantiated body, so it
may be reused as an endpoint join of a further cast or another consumer. -/
theorem RecursiveCastCompute.inst_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (RX : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ y) shared) :
    ∃ z, env.HasType univs Γ z A ∧ proofErase Γ z = shared ∧
      RecursiveCastCompute D (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (proofErase Γ (b.inst z)) ∧
      RecursiveCastCompute D (proofEraseCtx Γ)
        (proofErase Γ (b.inst y)) (proofErase Γ (b.inst z)) := by
  obtain ⟨z, HZ, EZ⟩ := RX.realize heq hs hregistry hΓA.1 hx
  refine ⟨z, HZ.hasType.2, EZ, ?_, ?_⟩
  · exact (EZ ▸ RX).inst_argument hΓA hb hx HZ.hasType.2
  · exact (EZ ▸ RY).inst_argument hΓA hb hy HZ.hasType.2

/-- Independent beta tails of an explicit recursive join have an actual
certified computation join, hence comparisons in either checking mode. This
uses beta commutation and beta confluence at the realized shared output only. -/
theorem RecursiveCastCompute.join_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ b) shared)
    (PA : ProofShape.BetaRed (proofErase Γ a) left)
    (PB : ProofShape.BetaRed (proofErase Γ b) right) :
    ∃ out, ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) left out ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) right out := by
  obtain ⟨l, BL, CL⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ ha
    (RA.certified heq hs hregistry) PA
  obtain ⟨r, BR, CR⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ hb
    (RB.certified heq hs hregistry) PB
  obtain ⟨e, HE, EE⟩ := RA.realize heq hs hregistry hΓ ha
  rw [← EE] at BL BR
  obtain ⟨out, LL, LR⟩ := proofErase_beta_confluent hΓ HE.hasType.2 BL BR
  exact ⟨out, CL.trans (.beta LL), CR.trans (.beta LR)⟩

end Lean4Lean.VEnv.Strengthening
