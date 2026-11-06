import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveCastComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Higher-order consumers of recursively certified casts

Argument computation is propagated through every occurrence in an arbitrary
typed body, retaining the recursive computation certificate itself. Its checked
interpretation then supplies all future beta and typed-substitution comparisons.
These conclusions do not assert arbitrary full-core or higher-stage confluence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A computation of the argument propagates through any typed consumer,
including duplicated occurrences and occurrences in function position. The
result retains the same recursive grammar, without an image recovery premise. -/
theorem RecursiveCastCompute.inst_argument
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    RecursiveCastCompute D (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have WX := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have WY := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := y) (A₀ := A)).substEq hΓA hy
  suffices H : RecursiveCastCompute D (proofEraseCtx Γ)
    (proofErase Γ (b.subst (VExpr.Subst.cons VExpr.Subst.id x)))
    (proofErase Γ (b.subst (VExpr.Subst.cons VExpr.Subst.id y))) by
    simpa only [VExpr.inst_eq] using H
  apply RecursiveCastCompute.images hΓA.1 WX WY hb
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .core .refl

/-- Explicit recursive joins construct a reusable future family comparison.
The common output need not normalize, and no global comparison stability is
assumed. Each cast's endpoint certificate was constructed by induction. -/
theorem RecursiveCastCompute.join_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ b) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) :=
  proofErase_certified_join_family heq hs hΓ ha hb
    (RA.certified heq hs hregistry) (RB.certified heq hs hregistry)

/-- The arbitrary consumer remains comparable after independent future beta
paths. The output retains its entire future certificate, as well as an actual
finite-stage comparison at the present residuals. -/
theorem RecursiveCastCompute.consumer_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y))
    (RX : ProofShape.BetaRed (proofErase Γ (b.inst x)) left)
    (RY : ProofShape.BetaRed (proofErase Γ (b.inst y)) right) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) left right ∧
    ∃ n, JointCompare (ErasedJointStage D n) (proofEraseCtx Γ) true left right := by
  have RC := R.inst_argument hΓA hb hx hy
  have HF := RC.join_family heq hs hregistry hΓA.1
    (hb.instN henv Ctx.InstN.zero hx) (hb.instN henv Ctx.InstN.zero hy) (.core .refl)
  exact ⟨HF.beta RX RY, (HF.1 RX RY).finite_stage erased_joint_stage_mono⟩

/-- Every typed reflexive cast supplies the recursive argument computation
with reflexive endpoint children. No endpoint comparison is a premise. -/
theorem recursive_reflexive_cast_consumer
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (hx : env.HasType univs Γ x X) (hb : env.HasType univs (X :: Γ) b B) :
    RecursiveCastCompute D (proofEraseCtx Γ)
      (proofErase Γ (b.inst (typeCast u X X q x))) (proofErase Γ (b.inst x)) :=
  (RecursiveCastCompute.cast hu hΓ hX hX hq hx (.core .refl) (.core .refl)).inst_argument
    ⟨hΓ, u, hX⟩ hb (HasType.typeCast henv heq hu hX hX hq hx) hx

/-- A cast whose target is itself a cast can be consumed by any typed body.
The inner cast constructs both endpoint join paths for the outer cast; its
outer equality witness and the common argument typing are also constructed.
Thus this is a genuinely recursive instance of the consumer theorem. -/
theorem recursive_nested_cast_consumer
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hx : env.HasType univs Γ x X)
    (hr : env.HasType univs Γ r
      (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)))
    (hb : env.HasType univs (typeCast (.succ u) (.sort u) (.sort u) r X :: Γ) b B) :
    let Y := typeCast (.succ u) (.sort u) (.sort u) r X
    let p := eqReflApp (.succ u) (.sort u) X
    RecursiveCastCompute D (proofEraseCtx Γ)
      (proofErase Γ (b.inst (typeCast u X Y p x))) (proofErase Γ (b.inst x)) := by
  dsimp only
  have HI := IsDefEq.typeCast_refl henv heq (u := .succ u) (by exact hu) hΓ
    (HasType.sort hu) hr hX
  have HP := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HI.symm).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  have HC := HasType.typeCast henv.ordered heq hu hX HI.hasType.1 HP hx
  have RX : RecursiveCastCompute D (proofEraseCtx Γ)
      (proofErase Γ (typeCast (.succ u) (.sort u) (.sort u) r X)) (proofErase Γ X) :=
    .cast (by exact hu) hΓ (HasType.sort hu) (HasType.sort hu) hr hX (.core .refl) (.core .refl)
  exact (RecursiveCastCompute.cast hu hΓ hX HI.hasType.1 HP hx (.core .refl) RX).inst_argument
    ⟨hΓ, u, HI.hasType.1⟩ hb HC (HI.symm.defeq hx)

omit [Params] in
/-- In every actual canonical-Eq environment, arbitrary typed consumers of a
recursive cast computation retain future comparison after independent beta
paths. All soundness and Eq registry premises are discharged. -/
theorem EnvironmentCore.recursive_cast_consumer_beta {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A b B x y left right}, env.HasCanonicalEq → OnCtx (A :: Γ) (env.IsType U) →
      env.HasType U (A :: Γ) b B → env.HasType U Γ x A → env.HasType U Γ y A →
      RecursiveCastCompute definitions (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) →
      ProofShape.BetaRed (proofErase Γ (b.inst x)) left →
      ProofShape.BetaRed (proofErase Γ (b.inst y)) right →
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion definitions) Δ true)
        (proofEraseCtx Γ) left right ∧
      ∃ n, JointCompare (ErasedJointStage definitions n) (proofEraseCtx Γ) true left right := by
  letI := henv.params U
  intro Γ A b B x y left right heq hΓA hb hx hy R RX RY
  exact R.consumer_beta heq sound rfl hΓA hb hx hy RX RY

end Lean4Lean.VEnv.Strengthening
