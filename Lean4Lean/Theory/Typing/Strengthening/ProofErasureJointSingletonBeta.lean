import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral
import Lean4Lean.Theory.Typing.Strengthening.PrefixProgramCongruence

/-! # Beta residuals of general joint singleton guards

Argument beta reduction computes both family templates. Proposition beta
stability preserves their comparison, and typed identity substitution moves it
to the new residual telescope. The same premise therefore supplies the guard
needed at the argument-reduced prefix, with no additional guard-coverage law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open PureObservation
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

omit [Params] in
private theorem beta_subst (H : VExpr.BetaRed e out) :
    VExpr.BetaRed (e.subst σ) (out.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | beta => rw [VExpr.subst_inst]; exact .beta

omit [Params] in
private theorem beta_congrRel : CongrRel (fun _ => VExpr.BetaRed) where
  rfl := .refl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN _ R := by
    simp only [← lift'_consN_skipN, RecursorData.lift'_eq_subst]
    exact beta_subst R

omit [Params] in
private theorem beta_opened_arguments {data : RecursorData}
    (HA : List.Forall₂ VExpr.BetaRed args args') :
    List.Forall₂ VExpr.BetaRed (data.openedArguments args) (data.openedArguments args') := by
  unfold RecursorData.openedArguments
  rw [← HA.length_eq]
  apply List.Forall₂.append'
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply HA.imp
    intro a b R
    simp only [← lift'_consN_skipN, RecursorData.lift'_eq_subst]
    exact beta_subst R
  · exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)

/-- Transport a family comparison through original beta paths and a converted
context in one invocation. The source and target comparators may differ. -/
def ErasedFamilyContextBetaTransport
    (Cmp Cmp' : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₁ Γ₂ P Q P' Q'}, OnCtx Γ (env.IsType univs) →
    IsDefEqCtx env univs Γ Γ₁ Γ₂ →
    env.HasType univs Γ₁ P (.sort .zero) → env.HasType univs Γ₁ Q (.sort .zero) →
    Cmp (proofEraseCtx Γ₁) (proofErase Γ₁ P) (proofErase Γ₁ Q) →
    VExpr.BetaRed P P' → VExpr.BetaRed Q Q' →
    Cmp' (proofEraseCtx Γ₂) (proofErase Γ₂ P') (proofErase Γ₂ Q')

/-- Full-union proposition beta stability supplies combined beta and context
transport for family guards. -/
theorem JointPropBetaStability.family_transport
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedFamilyContextBetaTransport (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true)
      (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true) := by
  intro Γ Γ₁ Γ₂ P Q P' Q' hΓ W hP hQ H RP RQ
  have hΓ₁ : OnCtx Γ₁ (env.IsType univs) := by
    clear hP hQ H
    induction W with
    | zero => exact hΓ
    | succ _ hA ih => exact ⟨ih, _, hA.hasType.1⟩
  have hP' := (beta_eq hΓ₁ hP RP).hasType.2
  have hQ' := (beta_eq hΓ₁ hQ RQ).hasType.2
  have H' := Hbeta.defeqCtx heq hs hΓ W hP' hQ'
    (Hbeta.forward hΓ₁ hP hQ H
      (proofErase_beta_forward hΓ₁ hP RP) (proofErase_beta_forward hΓ₁ hQ RQ))
  rwa [proofErase_defeqCtx hΓ₁ W hP', proofErase_defeqCtx hΓ₁ W hQ'] at H'

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- Combined family transport lifts to beta reduction of all supplied
arguments, including conversion of the entire generated residual telescope.
The source and target family comparators may differ. -/
theorem Valid.family_guard_beta_with (V : C.Valid) (heq : env.HasCanonicalEq)
    (Htransport : ErasedFamilyContextBetaTransport Cmp Cmp')
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (hg' : C.data.singletonUnfolding env univs C.levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HA : List.Forall₂ VExpr.BetaRed args args')
    (HG : GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison Cmp)
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison Cmp')
      Γ C.data C.levels args' program' C.layout C.elim := by
  have Rsource : VExpr.BetaRed
      (mkApps (.const C.data.name C.levels) args)
      (mkApps (.const C.data.name C.levels) args') :=
    beta_congrRel.mkApps (Γ := Γ) .refl HA
  have hsource := V.registered.prefixType henv hΓ V.levels_wf hg ht
  have HE := beta_eq hΓ hsource Rsource
  have ht' : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args') :=
    ⟨_, HE.hasType.2⟩
  have hsource' := V.registered.prefixType henv hΓ V.levels_wf hg' ht'
  have htypes := HE.hasType.2.uniqU henv hΓ hsource'
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  obtain ⟨_, _, _, _, hlenD', _, _⟩ := RecursorData.singletonUnfolding_layout hg'
  have hlenDomains : program.domains.length = program'.domains.length := by
    rw [hlenD, hlenD', HA.length_eq]
  have Wctx := IsDefEqU.wrapForalls_context henv hΓ
    (.zero : IsDefEqCtx env univs Γ Γ Γ) hlenDomains htypes
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, E, hS, hE, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, hidx, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  obtain ⟨_, hps', _, hidx', _, _, _⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg' ht' WF
  let ps := (C.data.openedArguments args).take C.data.numParams
  let idx := ((C.data.openedArguments args).drop C.data.indexOffset).take C.data.numIndices
  let ps' := (C.data.openedArguments args').take C.data.numParams
  let idx' := ((C.data.openedArguments args').drop C.data.indexOffset).take C.data.numIndices
  have Hall := beta_opened_arguments (data := C.data) HA
  have Hcaps : List.Forall₂ (VExpr.BetaRed)
      (ps ++ idx ++ [.bvar 0]) (ps' ++ idx' ++ [.bvar 0]) :=
    ((Lean4Lean.List.forall₂_take Hall _).append'
      (Lean4Lean.List.forall₂_take (Lean4Lean.List.forall₂_drop Hall _) _)).append' (.cons .refl .nil)
  have RF := beta_congrRel.instantiateParams_args (Γ := [])
    (e := transportedFamily C.layout (C.data.propParams C.levels) C.elim
      (genericPa C.layout (C.data.propParams C.levels)) (genericIa C.layout) (.bvar 0)) Hcaps
  rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
    transportedFamily_generic_inst heq WF hps hidx,
    transportedFamily_generic_inst heq WF hps' hidx'] at RF
  have RP := beta_congrRel.instantiateParams_args (Γ := [])
    (e := mkApps C.elim.family
      (genericPa C.layout (C.data.propParams C.levels) ++ genericIa C.layout)) Hcaps
  rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
    requestedFamily_generic_inst WF hps hidx,
    requestedFamily_generic_inst WF hps' hidx'] at RP
  have hF := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hP := WF.family_prop henv hps hargs
  exact Htransport hΓ Wctx hF hP HG RF RP

/-- Proposition beta stability transports every general joint family guard
through beta reduction of all supplied arguments, including conversion of the
entire generated residual telescope. No extra guard-transport premise is used. -/
theorem Valid.joint_family_guard_beta (V : C.Valid) (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (hg' : C.data.singletonUnfolding env univs C.levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HA : List.Forall₂ VExpr.BetaRed args args')
    (HG : GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true))
      Γ C.data C.levels args' program' C.layout C.elim :=
  V.family_guard_beta_with heq (Hbeta.family_transport heq hs) hΓ hg hg' ht HA HG

end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
