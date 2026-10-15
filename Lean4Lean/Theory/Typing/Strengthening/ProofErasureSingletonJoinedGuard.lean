import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonCoreResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTypedSingletonStages

/-! # Transporting computationally joined singleton family guards

The two family endpoints specialize fixed typed templates. Computation of
supplied arguments computes both endpoints in the old opened context. Typed
core confluence preserves their literal join, and conversion of the residual
telescope identifies the new endpoints' erasures in the new opened context.
This covers common-reduct guards for arbitrary singleton layouts. It does not
assert transport of every recursive contextual comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open PureObservation
open private core_arguments_replay from Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonCoreResidual
variable [Params]

/-- A family certificate witnessed by an exact ordinary computational join.
It uses the actual stored definitions and selected structure equations. -/
def CoreFamilyJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ shared, ProofShape.Compute ErasedCore.Step (proofErase Γ a) shared ∧
    ProofShape.Compute ErasedCore.Step (proofErase Γ b) shared

/-- A literal family join is a stage-zero scoped comparison certificate. -/
theorem CoreFamilyJoin.scoped (H : CoreFamilyJoin Γ a b) :
    GuardedSingleton.ScopedFamilyComparison (fun _ => ErasedCore.Step) Γ a b := by
  obtain ⟨shared, HA, HB⟩ := H
  exact .compute (HA.scoped (fun H => .base H)) (HB.scoped (fun H => .base H)) .refl

private theorem core_opened_arguments {data : RecursorData}
    (HA : List.Forall₂ (PatternCompute D) args args') :
    List.Forall₂ (PatternCompute D) (data.openedArguments args) (data.openedArguments args') := by
  unfold RecursorData.openedArguments
  rw [← HA.length_eq]
  apply List.Forall₂.append'
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply HA.imp
    intro a b R
    simp only [← lift'_consN_skipN, RecursorData.lift'_eq_subst]
    exact R.subst
  · exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- A joined family guard survives arbitrary ordinary computation of supplied
arguments. The old and new generated telescopes may differ. Source typing and
ordinary congruence align those contexts; no unfolding check at either program
or erased guard-transport assumption is required. -/
theorem Valid.joined_guard_core (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (hg' : C.data.singletonUnfolding env univs C.levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HA : List.Forall₂ (PatternCompute ErasedCore.definitions) args args')
    (HG : GuardedSingleton.FamilyGuard CoreFamilyJoin
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard CoreFamilyJoin
      Γ C.data C.levels args' program' C.layout C.elim := by
  have hs : ErasedCore.definitions.Sound env univs :=
    RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have Rsource : PatternCompute ErasedCore.definitions
      (mkApps (.const C.data.name C.levels) args)
      (mkApps (.const C.data.name C.levels) args') :=
    patternCompute_congrRel.mkApps (Γ := Γ) .refl HA
  have hsource := V.registered.prefixType henv hΓ V.levels_wf hg ht
  have HE := Rsource.simAt hs hΓ _ hsource
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
  have Hall := core_opened_arguments (data := C.data) HA
  have Hcaps : List.Forall₂ (PatternCompute ErasedCore.definitions)
      (ps ++ idx ++ [.bvar 0]) (ps' ++ idx' ++ [.bvar 0]) :=
    ((Lean4Lean.List.forall₂_take Hall _).append'
      (Lean4Lean.List.forall₂_take (Lean4Lean.List.forall₂_drop Hall _) _)).append' (.cons .refl .nil)
  have RF := patternCompute_congrRel.instantiateParams_args (Γ := [])
    (e := transportedFamily C.layout (C.data.propParams C.levels) C.elim
      (genericPa C.layout (C.data.propParams C.levels)) (genericIa C.layout) (.bvar 0)) Hcaps
  rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
    transportedFamily_generic_inst heq WF hps hidx,
    transportedFamily_generic_inst heq WF hps' hidx'] at RF
  have RP := patternCompute_congrRel.instantiateParams_args (Γ := [])
    (e := mkApps C.elim.family
      (genericPa C.layout (C.data.propParams C.levels) ++ genericIa C.layout)) Hcaps
  rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
    requestedFamily_generic_inst WF hps hidx,
    requestedFamily_generic_inst WF hps' hidx'] at RP
  have hF := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hP := WF.family_prop henv hps hargs
  have EF := proofErase_defeqCtx hctx Wctx (RF.simAt hs hctx _ hF).hasType.2
  have EP := proofErase_defeqCtx hctx Wctx (RP.simAt hs hctx _ hP).hasType.2
  obtain ⟨shared, HF, HP⟩ := HG
  obtain ⟨out, HL, HR⟩ := ErasedCore.join_forward hcon hctx hF hP HF HP
    (proofErase_pattern_compute_forward hs hcon hctx hF RF)
    (proofErase_pattern_compute_forward hs hcon hctx hP RP)
  rw [EF] at HL
  rw [EP] at HR
  exact ⟨out, HL, HR⟩

/-- General singleton unfolding with a joined family guard commutes with
arbitrary finite raw core computation of all supplied arguments. Both prefix
edges are certified at stage one, and both horizontal edges use only core
computation. New original arguments and the checked generated output are
reconstructed; whole-proof sources are included by forward erasure. -/
theorem Valid.joined_prefix_core_peak (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard CoreFamilyJoin
      Γ C.data C.levels args program C.layout C.elim)
    (HA : List.Forall₂ (ProofShape.Compute ErasedCore.Step) (args.map (proofErase Γ)) rawArgs) :
    ∃ args' program', args'.map (proofErase Γ) = rawArgs ∧
      C.data.singletonUnfolding env univs C.levels args' = some program' ∧
      ProofShape.Compute ErasedCore.Step
        (proofErase Γ (mkApps (.const C.data.name C.levels) args))
        (proofErase Γ (mkApps (.const C.data.name C.levels) args')) ∧
      ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage ErasedCore.definitions 1)
        (proofEraseCtx Γ) (proofErase Γ (mkApps (.const C.data.name C.levels) args))
        (proofErase Γ program.rhs) ∧
      ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage ErasedCore.definitions 1)
        (proofEraseCtx Γ) (proofErase Γ (mkApps (.const C.data.name C.levels) args'))
        (proofErase Γ program'.rhs) ∧
      ProofShape.Compute ErasedCore.Step (proofErase Γ program.rhs) (proofErase Γ program'.rhs) := by
  have hs : ErasedCore.definitions.Sound env univs :=
    RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have hstep : ErasedScopedPrimitiveDescent
      (ErasedScopedTypedSingletonStage ErasedCore.definitions 0) :=
    erased_scoped_typed_singleton_stage_descent heq hs 0
  have HGS : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison
        (ErasedScopedTypedSingletonStage ErasedCore.definitions 0))
      Γ C.data C.levels args program C.layout C.elim := HG.scoped
  have HC := V.check heq hstep hΓ hg ht HGS
  obtain ⟨args', Hargs, Eargs⟩ := core_arguments_replay hs hΓ
    (mkApps_arguments_wf henv hΓ ht).2 HA
  obtain ⟨program', hg'⟩ := RecursorData.singletonUnfolding_sameArity hg Hargs.length_eq.symm
  have HG' := V.joined_guard_core heq hcon hΓ hg hg' ht Hargs HG
  have HGS' : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison
        (ErasedScopedTypedSingletonStage ErasedCore.definitions 0))
      Γ C.data C.levels args' program' C.layout C.elim := HG'.scoped
  have Rsource : PatternCompute ErasedCore.definitions
      (mkApps (.const C.data.name C.levels) args)
      (mkApps (.const C.data.name C.levels) args') :=
    patternCompute_congrRel.mkApps (Γ := Γ) .refl Hargs
  have ht' : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args') :=
    ⟨_, (Rsource.simAt hs hΓ _ HC.source_typed).hasType.2⟩
  have HC' := V.check heq hstep hΓ hg' ht' HGS'
  have HP : PrefixUnfold env univs recursorData Γ C.data.name C.levels args program.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC
  have HP' : PrefixUnfold env univs recursorData Γ C.data.name C.levels args' program'.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg' HC'
  have Rout := singleton_program_congr patternCompute_congrRel HP HP' (Γ := Γ) Hargs
  refine ⟨args', program', Eargs, hg',
    proofErase_pattern_compute_forward hs hcon hΓ HC.source_typed Rsource, ?_, ?_,
    proofErase_pattern_compute_forward hs hcon hΓ (HC.defeq henv hΓ).hasType.2 Rout⟩
  · exact proofErase_scoped_typed_singleton_stage_forward heq hΓ V.lookup V.registered
      V.large V.zero V.levels_wf V.recType_eq V.layout_eq V.elim_eq hg HC HGS
  · exact proofErase_scoped_typed_singleton_stage_forward heq hΓ V.lookup V.registered
      V.large V.zero V.levels_wf V.recType_eq V.layout_eq V.elim_eq hg' HC' HGS'

end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
