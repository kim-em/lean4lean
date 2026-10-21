import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrierPrefixes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedSubsingleton

/-! # Future carrier checking from actual type comparisons

At sort-typed endpoints the whole future comparison can be read in inferred
mode. Rigid empty-family exposure then gives future carrier checking without
a prescribed computation path. For structural subsingletons, an ordinary
certified type comparison already supplies a certified exposure path and hence
a full future carrier certificate, including arbitrary dependent Pi telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Independently sort-typed endpoints admit inferred checking at every future
beta residual and interpreted substitution. Neither a substitution law for
primitives nor a general endpoint transport law is required: the input retains
its own future comparisons. -/
theorem BetaStableFamily.types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ false)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B) := by
  have local_infer {Γ A B u v a b} (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
      (RA : ProofShape.BetaRed (proofErase Γ A) a)
      (RB : ProofShape.BetaRed (proofErase Γ B) b)
      (HC : JointCompare Step (proofEraseCtx Γ) mode a b) :
      JointCompare Step (proofEraseCtx Γ) false a b := by
    obtain ⟨A', PA, EA⟩ := proofErase_beta_replay hΓ hA RA
    obtain ⟨B', PB, EB⟩ := proofErase_beta_replay hΓ hB RB
    rw [← EA, ← EB] at HC ⊢
    exact proofErase_joint_types_inferred hstep hΓ
      (beta_eq hΓ hA PA).hasType.2 (beta_eq hΓ hB PB).hasType.2 HC
  refine ⟨fun RA RB => local_infer hΓ hA hB RA RB (H.1 RA RB), ?_⟩
  intro Δ' τ a b W RA RB
  have HC := H.2 W RA RB
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS hA ES] at RA
  rw [← proofErase_subst_with hΓ₀ WS hB ES] at RB
  rw [← EΓ₀] at HC ⊢
  exact local_infer hΓ₀ (hA.subst henv WS) (hB.subst henv WS) RA RB HC

/-- An inferred future comparison from a displayed empty registered family
provides every future endpoint guard at the target carrier. Each future target
carrier is exposed independently; no global computation confluence or primitive
substitution law is assumed. Parameters may themselves contain redexes. -/
theorem BetaStableFamily.unit_carrier
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ false)
      Δ (mkApps (.const family ls) ps) T) :
    BetaStableCarrier Step Δ T a b := by
  refine ⟨fun RC _ _ => (H.1 .refl RC).unit_carrier_target hn hi hx hf hp, ?_⟩
  intro Δ' τ C p q W RC _ _
  have HC := H.2 W .refl RC
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HC
  exact HC.unit_carrier_target hn hi hx hf (by simpa only [List.length_map] using hp)

/-- A future comparison between actual types transports the empty-family
carrier fragment, in either input mode. The target is the same relation, even
when no global substitution law is known for that relation. -/
theorem proofErase_future_unit_carrier
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ U))
    (ET : proofErase Γ T = ProofShape.mkApps (.const family ls) ps) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ U) a b := by
  have HC := H.types_inferred hstep hΓ hT hU
  rw [ET] at HC
  exact HC.unit_carrier hn hi hx hf hp

/-- An ordinary certified comparison from a structural subsingleton type
already constructs a full future guard at the target. The comparison need not
carry a future certificate: its certified exposure path commutes with future
beta and substitutes, and the exposed structural certificate is itself stable.
This includes arbitrary dependent Pi telescopes ending in an empty structure. -/
theorem proofErase_certified_compared_subsingleton_future
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ U) a b := by
  have hinert {family info Δ ls args out} (hi : env.projections family info) :
      ¬ ErasedBetaStableJoint D Δ (mkApps (.const family ls) args) out := by
    intro H
    exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) (hD hi)
      (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)
  obtain ⟨out, R, Hout⟩ := proofErase_joint_compared_subsingleton_compute
    (erased_beta_stable_joint_descent heq hs) erased_beta_stable_joint_head hinert
    (erased_beta_stable_joint_subst heq hs) hΓ hT hU HC HS
  exact (BetaStableCarrier.subsingleton Hout).certified_carrier_prefix heq hs hΓ hU R

end Lean4Lean.VEnv.Strengthening
