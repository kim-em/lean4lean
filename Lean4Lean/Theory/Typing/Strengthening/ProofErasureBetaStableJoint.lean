import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointParallelSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitutableParallelStrip
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelPrimitiveResidual

/-! # Joint primitives with beta-stable family certificates

This is a subset of existing joint computation, consisting of ordinary core
steps and general singletons whose guards retain future beta and substitution
certificates. Unlike arbitrary union primitives, these particular primitives
have the closure properties needed to iterate parallel commutation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private Compute.toParallel parallel_toCompute
  from Lean4Lean.Theory.Typing.Strengthening.DeclarationConfluence
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Existing core or general singleton computation with an actual union family
guard retaining all future beta and substitution comparisons. This relation
adds no reductions and is not defined recursively through its own comparison. -/
def ErasedBetaStableJoint (D : PureObservation.Definitions)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ErasedIotaPrimitive D a b ∨
    TypedSource Δ a ∧ SingletonPrimitiveWith
      (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)) Δ a b

/-- Forgetting the extra certificates includes every enriched primitive in the
original union, with exactly the same context and endpoints. -/
theorem erased_beta_stable_joint_into_union (H : ErasedBetaStableJoint D Δ a b) :
    ErasedJointUnion D Δ a b := by
  rcases H with H | ⟨HT, H⟩
  · exact ⟨0, H⟩
  · exact erased_joint_union_iff.2 (.inr (.inl ⟨HT, H.mono BetaStableFamily.base⟩))

/-- The enriched relation inherits typed descent from the existing joint union. -/
theorem erased_beta_stable_joint_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedBetaStableJoint D) :=
  fun hΓ hΓ' W ht H => erased_joint_union_descent heq hs hΓ hΓ' W ht
    (erased_beta_stable_joint_into_union H)

/-- Enriched primitives retain the existing constant/projection head restriction. -/
theorem erased_beta_stable_joint_head (H : ErasedBetaStableJoint D Δ a b) : PrimitiveHead a :=
  erased_joint_union_head (erased_beta_stable_joint_into_union H)

/-- Every interpreted substitution preserves this primitive relation itself.
The singleton branch uses its stored family certificate at the entire generated
residual telescope, without a beta-stability hypothesis for the union. -/
theorem erased_beta_stable_joint_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ErasedBetaStableJoint D Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    ErasedBetaStableJoint D Δ' (a.subst τ) (b.subst τ) := by
  rcases H with H | ⟨HT, H⟩
  · exact .inl (erased_iota_primitive_subst H)
  have hcmp : ErasedFamilyDescent
      (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)) :=
    beta_stable_family_descent (erased_joint_family_descent (erased_joint_union_descent heq hs))
  have HT' := HT.subst W
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  have HR : SingletonPrimitiveWith
      (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) (proofErase Γ e) b := by
    rw [EΓ, Ee]
    exact H
  have HR := proofErase_singleton_subst_with heq hcmp hcmp
    beta_stable_family_substitution hΓ₀ WS ES ht HR
  rw [EΓ₀, Ee] at HR
  exact .inr ⟨HT', HR⟩

/-- One parallel beta development of an enriched primitive has an enriched
primitive residual and one parallel output development. Its guard retains all
future certificates, so this theorem can be used again on the residual. -/
theorem erased_beta_stable_joint_parallel_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ErasedBetaStableJoint D Δ a b) (P : BetaPar a reduced) :
    ∃ shared, BetaPar b shared ∧ ErasedBetaStableJoint D Δ reduced shared := by
  rcases H with H | ⟨HT, H⟩
  · obtain ⟨shared, PB, HR⟩ := erased_iota_primitive_parallel_beta_residual H P
    exact ⟨shared, PB, .inl HR⟩
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨args', rfl, HA⟩ := P.const_spine
    obtain ⟨_, _, _, PB, HT', HR⟩ := V.parallel_beta_residual_with heq
      (beta_stable_family_descent (erased_joint_family_descent (erased_joint_union_descent heq hs)))
      beta_stable_family_transport HT ha hcalc HG HA
    exact ⟨_, PB, .inr ⟨HT', HR⟩⟩

/-- Parallel commutation now has the same enriched source and target relation,
so the path result retains the invariants needed by the next iteration. -/
theorem proofErase_beta_stable_joint_parallel_strip
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) reduced shared := by
  apply proofErase_scoped_parallel_beta_strip_to (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) ?_ hΓ ht R P
  intro Γ e T out reduced _ _ H P
  obtain ⟨shared, PB, HR⟩ := erased_beta_stable_joint_parallel_residual heq hs H P
  exact ⟨shared, PB, .base HR⟩

/-- Arbitrary finite beta commutes with enriched computation by iterating its
parallel strip. There is no global proposition beta-stability assumption: every
iteration uses the future certificates retained by the preceding residual. -/
theorem proofErase_beta_stable_joint_beta_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) reduced shared := by
  obtain ⟨eB, RB, EB⟩ := proofErase_beta_replay hΓ ht B
  have transport {e'} (P : ReflTransGen (ComputePar .empty) e e') :
      ∃ shared, ProofShape.BetaRed out shared ∧
        ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ e') shared := by
    induction P with
    | rfl => exact ⟨out, .refl, R⟩
    | tail initial step ih =>
      obtain ⟨middle, BM, RM⟩ := ih
      have hmid := (beta_eq hΓ ht (parallel_toCompute initial).to_beta).hasType.2
      have PB := proofErase_parallel_beta_forward hΓ hmid step
      obtain ⟨shared, PS, RS⟩ := proofErase_beta_stable_joint_parallel_strip heq hs hΓ hmid RM PB
      exact ⟨shared, BM.trans PS.toBeta, RS⟩
  obtain ⟨shared, BS, RS⟩ := transport (Compute.toParallel (Compute.of_beta (D := .empty) RB))
  exact ⟨shared, BS, EB ▸ RS⟩

end Lean4Lean.VEnv.Strengthening
