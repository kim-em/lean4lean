import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # Compared recovery of variables already contains the proposition front

Head exposure from a supplied type comparison is constructive. Obtaining such
comparisons for every typed variable is not a smaller remaining obligation:
just a fresh function variable at a proposition-domain Pi encodes the whole
proposition front. The recovered type is freely chosen in this test.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Missing assigned-type coverage for non-proof variables: choose any recovered
type and compare it in common mode with the variable's assigned type. Even this restriction
of general compared recovery implies PropositionFront under primitive descent,
as proved below. It is not a smaller sufficient strengthening obligation. -/
def JointVariableComparedRecovery
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ i T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.bvar i) T → ¬ IsProof Γ (.bvar i) →
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.bvar i)) out ∧
      JointCompare Step (proofEraseCtx Γ) true out (proofErase Γ T)

/-- Compared recovery of variables is already at least as strong as the entire
proposition front. A fresh non-proof variable declared at P -> Prop and assigned
R -> Prop supplies a comparison of those types, after composing its lookup path.
Both inserted binders then descend using the existing joint certificate theorem;
Pi injectivity recovers the original proposition equation below them. -/
theorem JointVariableComparedRecovery.implies_propositionFront
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : JointVariableComparedRecovery Step) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  let A : VExpr := .forallE P (.sort .zero)
  let B : VExpr := .forallE R (.sort .zero)
  have hA : env.HasType univs Γ A (.sort (.imax .zero (.succ .zero))) :=
    .forallE hP (.sort (by trivial))
  have hB : env.HasType univs Γ B (.sort (.imax .zero (.succ .zero))) :=
    .forallE hR (.sort (by trivial))
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hΓA : OnCtx (A.lift :: Q :: Γ) (env.IsType univs) := ⟨hΓQ, _, hA.weak henv⟩
  have HAB : env.IsDefEq univs (Q :: Γ) A.lift B.lift (.sort (.imax .zero (.succ .zero))) :=
    .forallEDF (HE.of_l henv hΓQ (hP.weak henv)) (.sortDF (by trivial) (by trivial) rfl)
  have hv : env.HasType univs (A.lift :: Q :: Γ) (.bvar 0) A.lift.lift := .bvar .zero
  have hvB : env.HasType univs (A.lift :: Q :: Γ) (.bvar 0) B.lift.lift :=
    (HAB.weak henv).defeq hv
  have hn : ¬ IsProof (A.lift :: Q :: Γ) (.bvar 0) := not_isProof_function_to_sort hΓA hv
  obtain ⟨out, HR, HC⟩ := H hΓA hvB hn
  rw [show proofErase (A.lift :: Q :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at HR
  have RT := HR.bvar_compute
  rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓA (Lookup.zero (ty := A.lift))] at RT
  have HC' : JointCompare Step (proofEraseCtx (A.lift :: Q :: Γ)) true
      (proofErase (A.lift :: Q :: Γ) A.lift.lift)
      (proofErase (A.lift :: Q :: Γ) B.lift.lift) := .compute RT .refl HC
  have W : Ctx.LiftN 2 0 Γ (A.lift :: Q :: Γ) := .zero [A.lift, Q]
  simp only [lift, liftN_liftN] at HC'
  rw [proofErase_liftN hΓ hΓA W hA, proofErase_liftN hΓ hΓA W hB] at HC'
  have Hbelow := (proofErase_joint_compare_descend hstep hΓ hΓA W rfl hA hB HC').1
    ⟨_, HasType.sort (by trivial)⟩
  exact ⟨_, (Hbelow.forallE_inv henv hΓ).1.choose_spec⟩

/-- The concrete joint union does not make variable compared-recovery coverage
a smaller front, including when its core contains the repaired quotient rule. -/
theorem jointVariableComparedRecovery_implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointVariableComparedRecovery (ErasedJointUnion D)) : PropositionFront :=
  H.implies_propositionFront (erased_joint_union_descent heq hs)

end Lean4Lean.VEnv.Strengthening
