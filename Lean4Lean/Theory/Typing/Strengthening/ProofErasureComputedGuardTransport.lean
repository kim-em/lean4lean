import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstrainedComputeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Substitution of recursive guards between arbitrary computation relations

The source and target may be different finite stages. This interface is used
with a proved exact-image transport theorem; it does not assert unrestricted
substitution or recovery completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim ProofShape
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- A binder-stable interpreted constraint together with proved transport of
both recursive source and target checking views. The generic primitive theorem uses
only these explicit fields; it assumes no unrestricted image coverage. -/
structure ComputedGuardSubstitution (Source Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop) : Prop where
  interpret : ∀ {Δ Δ' τ}, Transport Δ Δ' τ → ContextSubstitution Δ Δ' τ
  cons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ →
    Transport (A :: Δ) (A.subst τ :: Δ') τ.lift
  check : ∀ {Δ kind a b}, ComputedJointCheck Source Δ kind a b →
    ComputedJointTransportResult Transport Target Δ kind a b

/-- The guard-transport constraint extends through a realized dependent residual
telescope, with each annotation substituted at its actual depth. -/
theorem ComputedGuardSubstitution.telescope
    (G : ComputedGuardSubstitution Source Target Transport) {domains : List VExpr}
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    Transport (proofEraseCtx (domains.reverse ++ Γ))
      (proofEraseCtx ((domains.mapIdx fun i A => A.subst (σ.liftN i)).reverse ++ Γ₀))
      (τ.liftN domains.length) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => exact WR
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have WR' : Transport (proofEraseCtx (A :: Γ))
        (proofEraseCtx (A.subst σ :: Γ₀)) τ.lift := by
      simp only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA E]
      exact G.cons WR
    simp only [List.mapIdx_cons, VExpr.Subst.liftN,
      List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [← ProofShape.Subst.lift_liftN]
    have HI : Transport (proofEraseCtx (ds.reverse ++ A :: Γ))
        (proofEraseCtx ((ds.mapIdx fun i B => B.subst (σ.lift.liftN i)).reverse ++ A.subst σ :: Γ₀))
        (τ.lift.liftN ds.length) :=
      ih WR' hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx
    simp only [VExpr.Subst.lift_liftN, VExpr.Subst.liftN] at HI
    exact @HI

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- The actual family guard substitutes under its entire generated telescope.
The entire recursive source comparison transports, including computed applications. -/
theorem Valid.computed_family_guard_subst_between (V : C.Valid) (heq : env.HasCanonicalEq)
    (G : ComputedGuardSubstitution Source Target Transport)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ComputedJointCompare Source Δ true))
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
  have HC := G.check HG hctx htf hpf rfl rfl rfl
    (G.telescope WR hΓ₀ W E hctx)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode

/-- Typed general singleton primitives retain their exact output under an
interpreted guard-preserving substitution. The generated dependent telescope
is transported explicitly. -/
theorem proofErase_computed_singleton_guard_subst_between (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (htarget : ErasedScopedPrimitiveDescent Target) (G : ComputedGuardSubstitution Source Target Transport)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.ComputedJointCompare Source Δ true) (proofEraseCtx Γ) (proofErase Γ e) out) :
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
    have HC := V.checkWith heq (erased_computed_joint_family_descent hsource) W.wf hg ⟨_, ht⟩ HG
    have hg' := RecursorData.singletonUnfolding_subst henv V.registered V.large V.zero
      V.recType_eq (V.registered.recursorType_closed henv V.recType_eq) hg (σ := σ)
    have ht' : env.HasType univs Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) (T.subst σ) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using ht.subst henv.orderedStrong W hΓ₀
    have HG' := V.computed_family_guard_subst_between heq G hΓ₀ W E WR hg ⟨_, ht⟩ HG
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

/-- A specialized Eq prefix transports its actual carrier guard directly.
No encoding of Eq as a different singleton program or registry agreement is
needed for this source-typed substitution theorem. -/
theorem proofErase_computed_prefix_guard_subst_between
    (heq : env.HasCanonicalEq) (G : ComputedGuardSubstitution Source Target Transport)
    (hΓ : OnCtx Γ (env.IsType univs))
    (WR : Transport (proofEraseCtx Γ) Δ' τ)
    (ht : env.HasType univs Γ e T)
    (R : ComputedJointPrefixPrimitive Source
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive Target Δ'
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, _, _, Hb⟩ :=
      proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Hα, ← Ha, ← Hb] at HC
    obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := G.check HC hΓ ha hb rfl rfl rfl rfl WR
    rw [Hα, Ha, Hb] at HC'
    simpa only [ProofShape.eqRecBeforeMajor, ProofShape.eqProofType, ProofShape.subst,
      ProofShape.lift_subst_lift] using
      (ComputedJointPrefixPrimitive.intro (v := v) (w := w)
        (M := M.subst τ) (m := m.subst τ) HC')


end Lean4Lean.VEnv.Strengthening
