import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDisplayedLambdaPrefix
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSemanticSortReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure

/-! # Where reading a displayed lambda domain can add checking power

The local displayed-domain rule is already an ordinary application comparison
whenever its argument guard decodes to common checking. In particular it adds
no comparison at a domain definitionally equal to a universe, even if that
domain does not compute to a universe. Any potential gain must use a domain
that exposes a structure or a function. This does not prove strict extra
coverage there, or closure under arbitrary proposition substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Without structural carrier exposure, the old ordinary application rule
already accepts a displayed-domain certificate. No Pi recovery is needed. -/
theorem DisplayedLambdaApplication.joint_of_no_exposure
    (H : DisplayedLambdaApplication Step Δ (.app (.lam A body) x) (.app g y))
    (hn : ∀ {C}, ScopedCompute Step Δ A C → ¬ CarrierExposure C) :
    JointCompare Step Δ mode (.app (.lam A body) x) (.app g y) := by
  cases H with
  | intro HF HX => exact .app HF (HX.checked_of_no_exposure hn)

/-- Any possible additional comparison power requires an actually exposed
structural argument carrier. The alternative retains its computation path and
guard; it does not assert that the old comparison fails in that alternative. -/
theorem DisplayedLambdaApplication.joint_or_exposed
    (H : DisplayedLambdaApplication Step Δ (.app (.lam A body) x) (.app g y)) :
    JointCompare Step Δ mode (.app (.lam A body) x) (.app g y) ∨
      ∃ C, ScopedCompute Step Δ A C ∧ CarrierExposure C ∧
        JointCarrierGuard Step Δ C x y := by
  cases H with
  | intro HF HX =>
    rcases HX.checked_or_exposed with HC | HC
    · exact .inl (.app HF HC)
    · exact .inr HC

/-- At a domain equal to a universe, the displayed-domain certificate embeds
in ordinary comparison at the same computation relation. Actual equality of
the domain suffices; neither domain exposure nor lambda recovery is assumed. -/
theorem proofErase_displayed_lambda_universe_joint
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.sort v))
    (H : DisplayedLambdaApplication Step (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) body) x) (.app g y)) :
    JointCompare Step (proofEraseCtx Γ) mode
      (.app (.lam (proofErase Γ A) body) x) (.app g y) := by
  cases H with
  | intro HF HX =>
    exact .app HF (proofErase_joint_carrier_semantic_sort hstep hΓ hA HE HX)

/-- A universe-domain application guard already licenses the original joint
Eq prefix with its exact output. Thus the local new primitive is redundant in
this case, including converted universe annotations and arbitrary bodies. -/
theorem proofErase_displayed_lambda_universe_prefix
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.sort v))
    (H : DisplayedLambdaApplication Step (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) body) x) (.app g y)) :
    JointPrefixPrimitive Step (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor w z α (.app (.lam (proofErase Γ A) body) x)
        M m (.app g y))
      (.lam (eqProofType z α (.app (.lam (proofErase Γ A) body) x) (.app g y))
        (m.liftN 1)) :=
  .intro (.carrierChecked (proofErase_displayed_lambda_universe_joint hstep hΓ hA HE H))

/-- Over the existing full joint union, this prefix is already an old atomic
primitive, with the same source and output. No displayed-lambda extension
layer, extra recovery certificate, or computation simulation is required. -/
theorem proofErase_displayed_lambda_universe_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.sort v))
    (H : DisplayedLambdaApplication (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) body) x) (.app g y)) :
    ErasedJointUnion D (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor w z α (.app (.lam (proofErase Γ A) body) x)
        M m (.app g y))
      (.lam (eqProofType z α (.app (.lam (proofErase Γ A) body) x) (.app g y))
        (m.liftN 1)) :=
  erased_joint_union_iff.mpr (.inr (.inr
    (proofErase_displayed_lambda_universe_prefix
      (erased_joint_union_descent heq hs) hΓ hA HE H)))

end Lean4Lean.VEnv.Strengthening
