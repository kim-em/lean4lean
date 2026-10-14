import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonCode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTelescopeSubstitution

/-! # Simultaneous transport of generated singleton family certificates

Both family endpoints are typed before guard reflection. Their erasures and
scoped certificates therefore substitute beneath the entire residual telescope,
including its fresh proof marker and any dependent data indices.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
variable [Params]

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- A family certificate transports through any typed simultaneous substitution
when its recursive primitive relation transports through context interpretations.
No unfolding check or typing of the reconstructed bare fields is assumed. -/
theorem Valid.family_guard_subst (V : C.Valid) (heq : env.HasCanonicalEq)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
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
  have HC := HG.subst hsubst (ProofShape.ContextSubstitution.of_typed hctx₀ Wext Eext)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard GuardedSingleton.ScopedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
