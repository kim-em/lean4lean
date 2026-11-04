import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointRecoveringTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveringPrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Singleton computation under exact recoverable substitutions

Non-proof images supply exact recovery certificates in a separate relation.
Typed replay and image renaming preserve them under residual telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- The actual family guard transports under its entire generated telescope.
Only typed recoverable-image transport is required of recursive computation. -/
theorem Valid.computed_joint_family_guard_recovering (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : ProofShape.RecoveringPrimitiveTransport Image Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.RecoveringSubstitution Image (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ComputedJointCompare Step Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ComputedJointCompare Target Δ true))
      Γ₀ C.data C.levels (args.map (·.subst σ)) (program.subst σ) C.layout C.elim := by
  obtain ⟨_, hnon, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, F, hS, hF, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hF.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv W.wf V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  obtain ⟨hctx₀, Wext, Eext⟩ := erasedSubst_telescope hΓ₀ W E hctx
  let ps := (C.data.openedArguments args).take C.data.numParams
  let idx := ((C.data.openedArguments args).drop C.data.indexOffset).take C.data.numIndices
  have htf := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hpf := WF.family_prop henv hps hargs
  have htfS := transportedFamily_subst henv heq WF hctx hps hargs (σ.liftN program.domains.length)
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr hnon
  simp only [VExpr.subst_bvar, VExpr.Subst.liftN_apply, if_pos hpos] at htfS
  have hpfS : (mkApps C.elim.family (ps ++ idx)).subst (σ.liftN program.domains.length) =
      mkApps C.elim.family ((ps ++ idx).map (·.subst (σ.liftN program.domains.length))) := by
    rw [VExpr.subst_mkApps, WF.family_closed.subst_eq .zero]
  have HC := ProofShape.ComputedJointCompare.subst_recovering hstep hrename hinc htrans HG hctx htf hpf rfl rfl rfl
    (WR.telescope hrename hΓ₀ W E hctx)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode

/-- Typed general singleton primitives retain their exact output under an
interpreted recoverable-image substitution. Both relations need sound descent for replay. -/
theorem proofErase_computed_joint_singleton_recovering (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : ProofShape.RecoveringPrimitiveTransport Image Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.RecoveringSubstitution Image (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.ComputedJointCompare Step Δ true) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.ComputedJointCompare Target Δ true) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq W.wf ha ⟨_, ht⟩ hcalc HG
    have HC := V.checkWith heq (erased_computed_joint_family_descent hstep) W.wf hg ⟨_, ht⟩ HG
    have hg' := RecursorData.singletonUnfolding_subst henv V.registered V.large V.zero
      V.recType_eq (V.registered.recursorType_closed henv V.recType_eq) hg (σ := σ)
    have ht' : env.HasType univs Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) (T.subst σ) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using ht.subst henv.orderedStrong W hΓ₀
    have HG' := V.computed_joint_family_guard_recovering heq hstep hrename hinc htrans hΓ₀ W E WR hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq (erased_computed_joint_family_descent htarget) hΓ₀ hg' ⟨_, ht'⟩ HG'
    have hn' : ¬ IsProof Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using
        mt (isProof_subst hΓ₀ W ht).1 hn
    have HE := V.output_eq heq W.wf hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ₀ hg' HC' hn'
    have HS := proofErase_subst_with hΓ₀ W (HC.defeq henv W.wf).hasType.2 E
    rw [← program.subst_rhs (HC.templateScope henv).2.1, HE', HE] at HS
    rw [← hsrc, ← proofErase_subst_with hΓ₀ W ht E, VExpr.subst_mkApps, VExpr.subst_const,
      proofErase_const_spine hΓ₀ ht' hn', ← HS]
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ₀ hg' ⟨_, ht'⟩)
      ((V.guardWith_iff heq hΓ₀ hg' ⟨_, ht'⟩).2 HG')


namespace ProofShape
/-- Existence of a source realization discharges the typed premises for general
singleton transport; the generated code and output remain the same. -/
theorem ComputedJointSingletonPrimitive.subst_recovering (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : ErasedScopedPrimitiveDescent Target)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (H : ComputedJointSingletonPrimitive Step Δ e out) (WR : RecoveringSubstitution Image Δ Δ' τ) :
    ComputedJointSingletonPrimitive Target Δ' (e.subst τ) (out.subst τ) := by
  refine ⟨H.1.subst WR.interpretation, ?_⟩
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, HE⟩ := H.1
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := WR.interpretation hΓ EΓ
  have HR : SingletonPrimitiveWith (fun Δ => ComputedJointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) out := by
    rw [EΓ, HE]
    exact H.2
  have WR' : RecoveringSubstitution Image (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
    simpa only [EΓ, EΓ₀] using WR
  have HH := proofErase_computed_joint_singleton_recovering heq hstep htarget hrename hinc htrans hΓ₀ WS ES WR' ht HR
  rwa [EΓ₀, HE] at HH

end ProofShape

/-- Specialized Eq prefixes preserve their exact output under recoverable-image
transport. Source typing supplies the actual endpoints of the carrier guard. -/
theorem proofErase_computed_joint_prefix_recovering (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : ProofShape.RecoveringPrimitiveTransport Image Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (WR : ProofShape.RecoveringSubstitution Image Δ Δ' τ)
    (H : ProofShape.ComputedJointPrefixPrimitive Step Δ (proofErase Γ e) out) :
    ProofShape.ComputedJointPrefixPrimitive Target Δ' ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at H
  cases H with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := ProofShape.ComputedJointCarrierGuard.subst_recovering hstep hrename hinc htrans HC
      hΓ ha hb EΓ Hα Ha Hb WR
    simpa only [ProofShape.eqRecBeforeMajor, ProofShape.eqProofType, ProofShape.subst,
      ProofShape.lift_subst_lift] using
      (ProofShape.ComputedJointPrefixPrimitive.intro (v := v) (w := w) (M := M.subst τ) (m := m.subst τ) HC')

/-- Image recovery at stage r and source computation at stage n give typed
primitive transport at stage r+n. The proof uses the preceding source stage
for recursive guards and never assumes domain re-synthesis. -/
theorem erased_computed_joint_stage_recovering (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (imageStage : Nat) : ∀ stage,
    ProofShape.RecoveringPrimitiveTransport (ErasedComputedJointStage D imageStage)
      (ErasedComputedJointStage D stage) (ErasedComputedJointStage D (imageStage + stage)) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
    exact .base (erased_computed_joint_stage_mono (Nat.zero_le _) (erased_iota_primitive_subst H))
  | succ stage ih =>
    intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
    rcases H with H | H | H
    · exact (ih hΓ ht EΓ WR H).mono (erased_computed_joint_stage_mono (Nat.le_succ _))
    · exact .base (.inr (.inl (H.subst_recovering heq
        (erased_computed_joint_stage_descent heq hs stage)
        (erased_computed_joint_stage_descent heq hs (imageStage + stage))
        (erased_computed_joint_stage_rename heq hs imageStage)
        (erased_computed_joint_stage_mono (Nat.le_add_right imageStage stage)) ih WR)))
    · exact .base (.inr (.inr (proofErase_computed_joint_prefix_recovering heq
        (erased_computed_joint_stage_descent heq hs stage)
        (erased_computed_joint_stage_rename heq hs imageStage)
        (erased_computed_joint_stage_mono (Nat.le_add_right imageStage stage)) ih hΓ ht EΓ WR H)))

/-- Finite-stage recoverable images transport the entire joint union. Each
source primitive chooses its own finite stage and uses the additive bound. -/
theorem erased_computed_joint_union_recovering (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (imageStage : Nat) : ProofShape.RecoveringPrimitiveTransport
      (ErasedComputedJointStage D imageStage) (ErasedComputedJointUnion D) (ErasedComputedJointUnion D) := by
  intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
  obtain ⟨stage, H⟩ := H
  exact (erased_computed_joint_stage_recovering heq hs imageStage stage hΓ ht EΓ WR H).mono
    (fun H => ⟨imageStage + stage, H⟩)

end Lean4Lean.VEnv.Strengthening
