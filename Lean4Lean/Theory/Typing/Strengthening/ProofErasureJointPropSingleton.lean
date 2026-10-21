import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Actual singleton substitution from proposition comparison transport

The full dependent residual telescope is handled by simultaneous proposition
substitution between specified source and target relations. Full-union beta
stability remains one specialization of this directed transport interface.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]
/-- Typed proposition comparison transport from one primitive relation into
another. This is a directed interface, with no target-stability assumption. -/
def JointPropSubstitution
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₀ σ P Q}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    ProofShape.JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) →
    ProofShape.JointCompare Target (proofEraseCtx Γ₀) true
      (proofErase Γ₀ (P.subst σ)) (proofErase Γ₀ (Q.subst σ))

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- A family certificate transports through any typed simultaneous substitution
from the source to the target comparison relation. No unfolding check or
typing of the reconstructed bare fields is assumed. -/
theorem Valid.joint_family_guard_subst_with (V : C.Valid) (heq : env.HasCanonicalEq)
    (Hsubst : JointPropSubstitution Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
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
  have HC := Hsubst hctx₀ Wext htf hpf HG
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS]
  exact HC


end SingletonPrefixCode
/-- General raw singleton computation transports exactly through a typed source
substitution when proposition comparisons transport from source to target.
Both the residual telescope and literal output are transported; there is no
primitive-substitution or re-synthesis premise. -/
theorem proofErase_joint_singleton_subst_with (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (Hsubst : JointPropSubstitution Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
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
    have HG' := V.joint_family_guard_subst_with heq Hsubst hΓ₀ W E hg ⟨_, ht⟩ HG
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

/-- An interpreted context substitution transports a general singleton step
between specified guard relations, given typed proposition substitution.
Specialized carrier-guarded Eq steps must first be encoded as general steps. -/
theorem proofErase_joint_general_substitution_with
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (Hsubst : JointPropSubstitution Step Target)
    (H : ProofShape.JointSingletonPrimitive Step Δ a b)
    (W : ProofShape.ContextSubstitution Δ Δ' τ) :
    ProofShape.JointSingletonPrimitive Target Δ' (a.subst τ) (b.subst τ) := by
  have HT := H.1.subst W
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := H.1
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  have HR : ProofShape.SingletonPrimitiveWith
      (fun Δ => ProofShape.JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ e) b := by
    rw [EΓ, Ee]
    exact H.2
  have R := proofErase_joint_singleton_subst_with heq hstep htarget Hsubst hΓ₀ WS ES ht HR
  rw [EΓ₀, Ee] at R
  exact ⟨HT, R⟩

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- Full-union specialization using proposition beta stability. -/
theorem Valid.joint_family_guard_subst_of_prop_beta (V : C.Valid) (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true))
      Γ₀ C.data C.levels (args.map (·.subst σ)) (program.subst σ) C.layout C.elim :=
  V.joint_family_guard_subst_with heq (fun hΓ W hP hQ H => Hbeta.subst heq hs hΓ W hP hQ H)
    hΓ₀ W E hg ht HG
end SingletonPrefixCode

/-- Preserve the full-union singleton-substitution interface. -/
theorem proofErase_joint_singleton_subst_of_prop_beta (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) :=
  proofErase_joint_singleton_subst_with heq (erased_joint_union_descent heq hs)
    (erased_joint_union_descent heq hs) (fun hΓ W hP hQ H => Hbeta.subst heq hs hΓ W hP hQ H)
    hΓ₀ W E ht R

/-- Preserve the full-union primitive-substitution interface. -/
theorem proofErase_joint_general_substitution_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (H : ProofShape.JointSingletonPrimitive (ErasedJointUnion D) Δ a b)
    (W : ProofShape.ContextSubstitution Δ Δ' τ) :
    ErasedJointUnion D Δ' (a.subst τ) (b.subst τ) :=
  erased_joint_union_iff.2 (.inr (.inl (proofErase_joint_general_substitution_with heq
    (erased_joint_union_descent heq hs) (erased_joint_union_descent heq hs)
    (fun hΓ W hP hQ H => Hbeta.subst heq hs hΓ W hP hQ H) H W)))

end Lean4Lean.VEnv.Strengthening
