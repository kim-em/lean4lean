import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRetainedTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Transport of singleton computation with erased proof substitutions

Only retained variables need exact recovery images. Typed source replay keeps
that weaker invariant available under all singleton residual telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- Retained-variable transport extends through a realized dependent residual
telescope, with each annotation substituted at its actual depth. -/
theorem ProofShape.RetainedRenaming.telescope {domains : List VExpr}
    (WR : ProofShape.RetainedRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    ProofShape.RetainedRenaming (proofEraseCtx (domains.reverse ++ Γ))
      (proofEraseCtx ((domains.mapIdx fun i A => A.subst (σ.liftN i)).reverse ++ Γ₀))
      (τ.liftN domains.length) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => exact WR
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have WR' : ProofShape.RetainedRenaming (proofEraseCtx (A :: Γ))
        (proofEraseCtx (A.subst σ :: Γ₀)) τ.lift := by
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA E] using WR.cons (A := proofErase Γ A)
    simpa only [List.mapIdx_cons, VExpr.Subst.liftN, VExpr.Subst.lift_liftN,
      ProofShape.Subst.lift_liftN, List.length_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using
      ih WR' hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- The actual family guard transports under its entire generated telescope.
Only typed retained-variable transport is required of recursive computation. -/
theorem Valid.joint_family_guard_retained (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htrans : ProofShape.RetainedPrimitiveTransport Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.RetainedRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare Step Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare Target Δ true))
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
  have HC := ProofShape.JointCompare.rename_retained hstep htrans HG hctx htf hpf rfl rfl rfl
    (WR.telescope hΓ₀ W E hctx)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode

/-- Typed general singleton primitives retain their exact output under an
interpreted retained-variable substitution. Both relations need sound descent for replay. -/
theorem proofErase_joint_singleton_retained (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htrans : ProofShape.RetainedPrimitiveTransport Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.RetainedRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.JointCompare Step Δ true) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.JointCompare Target Δ true) (proofEraseCtx Γ₀)
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
    have HC := V.checkWith heq (erased_joint_family_descent hstep) W.wf hg ⟨_, ht⟩ HG
    have hg' := RecursorData.singletonUnfolding_subst henv V.registered V.large V.zero
      V.recType_eq (V.registered.recursorType_closed henv V.recType_eq) hg (σ := σ)
    have ht' : env.HasType univs Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) (T.subst σ) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using ht.subst henv.orderedStrong W hΓ₀
    have HG' := V.joint_family_guard_retained heq hstep htrans hΓ₀ W E WR hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq (erased_joint_family_descent htarget) hΓ₀ hg' ⟨_, ht'⟩ HG'
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
theorem JointSingletonPrimitive.rename_retained (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : ErasedScopedPrimitiveDescent Target)
    (htrans : RetainedPrimitiveTransport Step Target)
    (H : JointSingletonPrimitive Step Δ e out) (WR : RetainedRenaming Δ Δ' τ) :
    JointSingletonPrimitive Target Δ' (e.subst τ) (out.subst τ) := by
  refine ⟨H.1.subst WR.interpretation, ?_⟩
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, HE⟩ := H.1
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := WR.interpretation hΓ EΓ
  have HR : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) out := by
    rw [EΓ, HE]
    exact H.2
  have WR' : RetainedRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
    simpa only [EΓ, EΓ₀] using WR
  have HH := proofErase_joint_singleton_retained heq hstep htarget htrans hΓ₀ WS ES WR' ht HR
  rwa [EΓ₀, HE] at HH

end ProofShape

/-- Specialized Eq prefixes preserve their exact output under retained-variable
transport. Source typing supplies the actual endpoints of the carrier guard. -/
theorem proofErase_joint_prefix_retained (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htrans : ProofShape.RetainedPrimitiveTransport Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (WR : ProofShape.RetainedRenaming Δ Δ' τ)
    (H : ProofShape.JointPrefixPrimitive Step Δ (proofErase Γ e) out) :
    ProofShape.JointPrefixPrimitive Target Δ' ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at H
  cases H with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := ProofShape.JointCarrierGuard.rename_retained hstep htrans HC
      hΓ ha hb EΓ Hα Ha Hb WR
    simpa only [ProofShape.eqRecBeforeMajor, ProofShape.eqProofType, ProofShape.subst,
      ProofShape.lift_subst_lift] using
      (ProofShape.JointPrefixPrimitive.intro (v := v) (w := w) (M := M.subst τ) (m := m.subst τ) HC')

/-- Every concrete stage transports typed sources under retained renaming,
including substitution of proofs. The output stays at the same finite stage. -/
theorem erased_joint_stage_retained (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ProofShape.RetainedPrimitiveTransport (ErasedJointStage D stage) (ErasedJointStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
    exact .base (erased_iota_primitive_subst H)
  | succ stage ih =>
    intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
    rcases H with H | H | H
    · exact (ih hΓ ht EΓ WR H).mono (fun H => .inl H)
    · exact .base (.inr (.inl (H.rename_retained heq
        (erased_joint_stage_descent heq hs stage) (erased_joint_stage_descent heq hs stage) ih WR)))
    · exact .base (.inr (.inr (proofErase_joint_prefix_retained heq
        (erased_joint_stage_descent heq hs stage) ih hΓ ht EΓ WR H)))

/-- Selecting the finite source stage gives retained-variable transport of the
joint union, with no re-synthesis hypothesis. -/
theorem erased_joint_union_retained (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ProofShape.RetainedPrimitiveTransport (ErasedJointUnion D) (ErasedJointUnion D) := by
  intro Γ Δ Δ' τ e T out hΓ ht EΓ WR H
  obtain ⟨stage, H⟩ := H
  exact (erased_joint_stage_retained heq hs stage hΓ ht EΓ WR H).mono (fun H => ⟨stage, H⟩)

end Lean4Lean.VEnv.Strengthening
