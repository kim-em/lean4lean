import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFamilyCast

/-! # Consumers retain the joint recursive computation/comparison grammar

Cast computations justified by nonjoining endpoint comparisons propagate through
arbitrary typed bodies. Their future comparisons remain recursive certificates,
so they can justify a later cast, binder frame or paired instantiation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every occurrence of an argument computation is propagated by the images
constructor, retaining the joint grammar rather than only its interpretation. -/
theorem RecursiveFamilyCast.inst_argument
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    RecursiveFamilyCast D false (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have WX := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have WY := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := y) (A₀ := A)).substEq hΓA hy
  suffices H : RecursiveFamilyCast D false (proofEraseCtx Γ)
      (proofErase Γ (b.subst (VExpr.Subst.cons VExpr.Subst.id x)))
      (proofErase Γ (b.subst (VExpr.Subst.cons VExpr.Subst.id y))) by
    simpa only [VExpr.inst_eq] using H
  apply RecursiveFamilyCast.images hΓA.1 WX WY hb
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .prior (.core .refl)

/-- Independent beta residuals of arbitrary typed consumers retain recursive
comparison certificates. In particular a cast with nonjoining endpoint types
may be duplicated or used as a function before these residuals are compared. -/
theorem RecursiveFamilyCast.consumer_beta
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y))
    (RX : ProofShape.BetaRed (proofErase Γ (b.inst x)) left)
    (RY : ProofShape.BetaRed (proofErase Γ (b.inst y)) right) :
    RecursiveFamilyCast D true (proofEraseCtx Γ) left right :=
  .beta (.join hΓA.1 (hb.instN henv Ctx.InstN.zero hx) (hb.instN henv Ctx.InstN.zero hy)
    (R.inst_argument hΓA hb hx hy) (.prior (.core .refl))) RX RY

/-- Every recursive future comparison has a present finite joint-stage
certificate, with no asserted uniform bound over all future substitutions. -/
theorem RecursiveFamilyCast.finite_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (H : RecursiveFamilyCast D true Δ a b) :
    ∃ n, JointCompare (ErasedJointStage D n) Δ true a b :=
  (H.future heq hs hregistry).base.finite_stage erased_joint_stage_mono

/-- Computation also retains an actual finite stage at its exact endpoints. -/
theorem RecursiveFamilyCast.finite_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (H : RecursiveFamilyCast D false Δ a b) :
    ∃ n, ScopedCompute (ErasedJointStage D n) Δ a b :=
  ((H.certified heq hs hregistry).mono erased_beta_stable_joint_into_union).finite_stage erased_joint_stage_mono

omit [Params] in
/-- Actual canonical-Eq environments interpret recursive consumer residuals
with a retained grammar certificate and a finite comparison. Soundness and
registry agreement are discharged from the environment itself. -/
theorem EnvironmentCore.recursive_family_consumer_beta {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A b B x y left right}, env.HasCanonicalEq → OnCtx (A :: Γ) (env.IsType U) →
      env.HasType U (A :: Γ) b B → env.HasType U Γ x A → env.HasType U Γ y A →
      RecursiveFamilyCast definitions false (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) →
      ProofShape.BetaRed (proofErase Γ (b.inst x)) left →
      ProofShape.BetaRed (proofErase Γ (b.inst y)) right →
      RecursiveFamilyCast definitions true (proofEraseCtx Γ) left right ∧
      ∃ n, JointCompare (ErasedJointStage definitions n) (proofEraseCtx Γ) true left right := by
  letI := henv.params U
  intro Γ A b B x y left right heq hΓA hb hx hy R RX RY
  have H := R.consumer_beta hΓA hb hx hy RX RY
  exact ⟨H, H.finite_compare heq sound rfl⟩

end Lean4Lean.VEnv.Strengthening
