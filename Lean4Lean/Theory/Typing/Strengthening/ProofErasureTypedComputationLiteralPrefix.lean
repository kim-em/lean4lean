import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGenericDataDomains

/-! # Singleton prefix computation at literal constructor indices

The actual opened prefix carries a typed literal field instance. Generic
data-domain chains supply its family chain; type-fork joining supplies a common
erased reduct, whose finite guard depth licenses the generated prefix step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Literal constructor evidence and generic data-domain chains provide an
actual finite-stage family guard. Type-fork joining is used only to join the
family chain; no all-prefix coverage or native argument recovery is assumed. -/
theorem SingletonPrefixCode.Valid.literal_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    {C : SingletonPrefixCode} (V : C.Valid)
    (HD : SingletonGenericDataDomainChains D C.layout (C.data.propParams C.levels) C.elim)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (HL : C.data.LiteralSingletonPrefix env univs Γ C.levels args program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args)) :
    ∃ stage, GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => ProofShape.CarrierRecoveredCompare
        (ErasedStaticStructureEtaExpansionStage D stage) Δ true))
      Γ C.data C.levels args program C.layout C.elim := by
  obtain ⟨S, E, fields, hS, hE, hf, hidx⟩ := HL
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := VEnv.RecursorData.singletonEquation_eq he
  obtain ⟨S, E, hS, hE, W⟩ := RecursorData.propElim_wf henv V.registered
    V.large V.zero V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args henv hΓ
    V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht W
  rw [hidx] at hargs
  have HC := HD.family_chain heq hs W hctx hps hargs hf
  obtain ⟨shared, RA, RB⟩ := HC.type_join heq hs HF hctx
  have HG : GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => ProofShape.CarrierRecoveredCompare
        (ErasedStaticStructureEtaExpansionUnion D) Δ true))
      Γ C.data C.levels args program C.layout C.elim := by
    change ProofShape.CarrierRecoveredCompare _ _ true _ _
    rw [hidx]
    exact .compute RA RB (.base (.leaf .refl))
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison at HG ⊢
  exact HG.finite_stage (fun {n m} hle {Δ a b} H =>
    erased_static_structure_eta_expansion_stage_mono hle H)

/-- A literal prefix computes at a finite stage derived from its family join.
The typed chain retains the original whole-prefix assignment. -/
theorem TypedComputationEq.literal_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    {C : SingletonPrefixCode} (V : C.Valid)
    (HD : SingletonGenericDataDomainChains D C.layout (C.data.propParams C.levels) C.elim)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (HL : C.data.LiteralSingletonPrefix env univs Γ C.levels args program)
    (ht : env.HasType univs Γ (mkApps (.const C.data.name C.levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const C.data.name C.levels) args) program.rhs T := by
  obtain ⟨stage, HG⟩ := V.literal_guard heq hs HF HD hΓ hg HL ⟨_, ht⟩
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D stage) :=
    erased_static_structure_eta_expansion_stage_descent heq hs stage
  have HC := V.checkWith heq (erased_carrier_recovered_family_descent hstep) hΓ hg ⟨_, ht⟩ HG
  have HE := (show env.IsDefEqU univs Γ _ _ from ⟨_, HC.defeq henv hΓ⟩).of_l henv hΓ ht
  refine .step HE ?_
  by_cases hp : IsProof Γ (mkApps (.const C.data.name C.levels) args)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  have EE := proofErase_const_spine hΓ ht hp
  have HT : ProofShape.TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const C.data.name C.levels) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, ht, EE⟩
  rw [EE, V.output_eq heq hΓ hg HC hp]
  exact .base ⟨stage + 1, .inr (.inl ⟨HT, .intro V (by simpa only [List.length_map] using ha)
    (V.telescope_eq hΓ hg ⟨_, ht⟩) ((V.guardWith_iff heq hΓ hg ⟨_, ht⟩).2 HG)⟩)⟩

/-- Registration and generation supply the fixed code certificate; only the
generic declaration-domain chains and actual literal occurrence are extra. -/
theorem TypedComputationEq.generated_literal_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (HD : ∀ S E, data.singletonLayout env levels = some S → data.propElim levels = some E →
      SingletonGenericDataDomainChains D S (data.propParams levels) E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HL : data.LiteralSingletonPrefix env univs Γ levels args program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const data.name levels) args) program.rhs T := by
  obtain ⟨recType, hrec⟩ := H.recursorType_exists
  obtain ⟨_, _, hlv, hlen, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  rw [hlv] at hlen
  have hnlevels := hlen.trans (RecursorData.singletonEquation_uvars heqn)
  obtain ⟨index, howner, _⟩ := VEnv.RecursorData.singletonEquation_eq heqn
  obtain ⟨S, E, hS, hE, _⟩ := RecursorData.propElim_wf henv H hl hz hw hnlevels ⟨index, howner⟩
  let C : SingletonPrefixCode := ⟨data, levels, args.length, recType,
    program.equation, program.equationBody, S, E⟩
  have V : C.Valid := ⟨hreg, H, hl, hz, hw, hrec, heqn, hbody, hS, hE, args, program, rfl, hg⟩
  exact TypedComputationEq.literal_prefix heq hs HF V (HD S E hS hE) hΓ rfl hg HL ht

end Lean4Lean.VEnv.Strengthening
