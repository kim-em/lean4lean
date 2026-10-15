import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Exact renaming of actual joint singleton primitives

The selected recovery types rename exactly throughout the residual telescope.
Consequently general singleton and specialized Eq prefixes transport without
assuming the open arbitrary-substitution re-synthesis law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- Exact context renaming extends through a realized dependent residual
telescope, with each annotation substituted at its actual depth. -/
theorem ProofShape.ContextRenaming.telescope {domains : List VExpr}
    (WR : ProofShape.ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    ProofShape.ContextRenaming (proofEraseCtx (domains.reverse ++ Γ))
      (proofEraseCtx ((domains.mapIdx fun i A => A.subst (σ.liftN i)).reverse ++ Γ₀))
      (τ.liftN domains.length) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => exact WR
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have WR' : ProofShape.ContextRenaming (proofEraseCtx (A :: Γ))
        (proofEraseCtx (A.subst σ :: Γ₀)) τ.lift := by
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA E] using WR.cons (A := proofErase Γ A)
    simpa only [List.mapIdx_cons, VExpr.Subst.liftN, VExpr.Subst.lift_liftN,
      ProofShape.Subst.lift_liftN, List.length_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using
      ih WR' hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- The actual family guard renames under its entire generated telescope.
Only primitive renaming is required of its recursive computation. -/
theorem Valid.joint_family_guard_rename (V : C.Valid) (heq : env.HasCanonicalEq)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
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
  have HC := HG.rename hrename (WR.telescope hΓ₀ W E hctx)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode

/-- Typed general singleton primitives retain their exact output under an
interpreted variable renaming. Both relations need sound descent for replay. -/
theorem proofErase_joint_singleton_rename (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : ProofShape.ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) (ht : env.HasType univs Γ e T)
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
    have HG' := V.joint_family_guard_rename heq hrename hΓ₀ W E WR hg ⟨_, ht⟩ HG
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
singleton renaming; the generated code and output remain the same. -/
theorem JointSingletonPrimitive.rename (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : ErasedScopedPrimitiveDescent Target)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (H : JointSingletonPrimitive Step Δ e out) (WR : ContextRenaming Δ Δ' τ) :
    JointSingletonPrimitive Target Δ' (e.subst τ) (out.subst τ) := by
  refine ⟨H.1.subst WR.interpretation, ?_⟩
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, HE⟩ := H.1
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := WR.interpretation hΓ EΓ
  have HR : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) out := by
    rw [EΓ, HE]
    exact H.2
  have WR' : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
    simpa only [EΓ, EΓ₀] using WR
  have HH := proofErase_joint_singleton_rename heq hstep htarget hrename hΓ₀ WS ES WR' ht HR
  rwa [EΓ₀, HE] at HH

/-- Specialized Eq prefixes rename directly with their joint carrier guards. -/
theorem JointPrefixPrimitive.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (H : JointPrefixPrimitive Step Δ e out) (WR : ContextRenaming Δ Δ' τ) :
    JointPrefixPrimitive Target Δ' (e.subst τ) (out.subst τ) := by
  cases H with
  | @intro α a b v w M m HC =>
    have HC' := HC.rename hrename WR
    simpa only [JointCheckKind.subst, eqRecBeforeMajor, eqProofType, ProofShape.subst,
      lift_subst_lift] using
      (JointPrefixPrimitive.intro (v := v) (w := w) (M := M.subst τ) (m := m.subst τ) HC')
end ProofShape

/-- Every actual finite joint stage preserves exact context renaming at the
same stage. This discharges primitive transport without joint re-synthesis. -/
theorem erased_joint_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage {Δ Δ' a b τ}, ErasedJointStage D stage Δ a b →
      ProofShape.ContextRenaming Δ Δ' τ →
      ErasedJointStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero => intro Δ Δ' a b τ H _; exact erased_iota_primitive_subst H
  | succ stage ih =>
    intro Δ Δ' a b τ H WR
    rcases H with H | H | H
    · exact .inl (ih H WR)
    · exact .inr (.inl (H.rename heq (erased_joint_stage_descent heq hs stage)
        (erased_joint_stage_descent heq hs stage) ih WR))
    · exact .inr (.inr (H.rename ih WR))

/-- The finite-stage union preserves exact renaming, with no growth of the
source stage needed by the construction. -/
theorem erased_joint_union_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ErasedJointUnion D Δ a b) (WR : ProofShape.ContextRenaming Δ Δ' τ) :
    ErasedJointUnion D Δ' (a.subst τ) (b.subst τ) := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_joint_stage_rename heq hs stage H WR⟩

end Lean4Lean.VEnv.Strengthening
