import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIndexComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta

/-! # Contracting a probe index is exactly proposition beta stability

Even at the fixed literal minor Prop, forward preservation of probe exposure
under beta contraction of its right index is equivalent to the earlier missing
proposition-checking beta law. Motive replacement does not supply this law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Missing forward index law: contracting the right proposition index of an
already exposed Eq probe preserves exposure. Only the fixed literal minor Prop
and the original constant motive are tested. This law is not proved here. -/
def EqProbeRightIndexBeta (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ P Q Q' q q'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ Q' (.sort .zero) →
    env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q) →
    env.HasType univs Γ q' (eqApp (.succ .zero) (.sort .zero) P Q') →
    BetaRed (proofErase Γ Q) (proofErase Γ Q') →
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe (.succ .zero) (.sort .zero) P Q q)) (.sort .zero) →
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe (.succ .zero) (.sort .zero) P Q' q')) (.sort .zero)

/-- Forward index-beta exposure at the fixed Prop probe is neither supplied by
motive replacement nor a new smaller beta obligation: it is exactly the missing
proposition beta-stability law. The converse realizes the arbitrary raw beta
output and constructs both equality majors from the input comparison itself. -/
theorem eqProbeRightIndexBeta_iff_prop_beta_stability
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs) :
    EqProbeRightIndexBeta D ↔ JointPropBetaStability (ErasedJointUnion D) := by
  constructor
  · intro H Γ P Q out hΓ hP hQ HC RB
    obtain ⟨Q', HE, EQ⟩ := proofErase_scoped_compute_realize
      (erased_joint_union_descent heq hs) hΓ hQ rfl rfl (ScopedCompute.beta RB)
    have hQ' := HE.hasType.2
    have HPQ := ((proofErase_joint_compare_reflect (erased_joint_union_descent heq hs)
      hΓ hP hQ HC).1 (.refl ⟨_, HasType.sort (by trivial)⟩)).of_l henv hΓ hP
    have hr := HasType.eqReflApp heq (U := univs) (Γ := Γ) (by trivial)
      (HasType.sort (by trivial)) hP
    have hq := (IsDefEq.eqApp_r heq (by trivial) (HasType.sort (by trivial)) hP HPQ).defeq hr
    have hq' := (IsDefEq.eqApp_r heq (by trivial) (HasType.sort (by trivial)) hP (HPQ.trans HE)).defeq hr
    have R := (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec (v := .zero)
      (by trivial) hΓ hP hQ hq).2 HC
    have R' := H hΓ hP hQ hQ' hq hq' (by simpa only [EQ] using RB) R
    rw [← EQ]
    exact (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec (v := .zero)
      (by trivial) hΓ hP hQ' hq').1 R'
  · intro H Γ P Q Q' q q' hΓ hP hQ hQ' hq hq' RB R
    have HC := (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec (v := .zero)
      (by trivial) hΓ hP hQ hq).1 R
    exact (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec (v := .zero)
      (by trivial) hΓ hP hQ' hq').2 (H hΓ hP hQ HC RB)

end Lean4Lean.VEnv.Strengthening
