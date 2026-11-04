import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredCongruence

/-! # Finite singleton stages with recovered-carrier family guards

General singleton family comparisons use CarrierRecoveredCompare, while
specialized Eq prefixes retain ComputedJointCarrierGuard. Recovery and all
computations use the preceding stage. The old computed stages embed at their
original bounds. No beta closure or declarative completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Recovered-carrier comparison supplies the generic family descent requirement. -/
theorem erased_carrier_recovered_family_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedFamilyDescent (fun Δ => ProofShape.CarrierRecoveredCompare Step Δ true) := by
  intro Γ Γ' n k P Q hΓ hΓ' W hP hQ HC
  exact ((proofErase_carrier_recovered_compare_descend hstep hΓ hΓ' W rfl hP hQ HC).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hΓ hP

namespace ProofShape
/-- Primitive inclusion preserves the entire recovered-carrier comparison. -/
theorem CarrierRecoveredCompare.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (H : CarrierRecoveredCompare Step Δ mode a b) : CarrierRecoveredCompare Target Δ mode a b := by
  induction H with
  | base H => exact .base (H.mono hstep)
  | recovered RA RB H => exact .recovered (RA.mono hstep) (RB.mono hstep) (H.mono hstep)
  | app HF HX ihf ihx => exact .app ihf ihx
  | proj H ih => exact .proj ih
  | lam HA HB ihA ihB => exact .lam ihA ihB
  | forallE HA HB ihA ihB => exact .forallE ihA ihB
  | compute RA RB H ih => exact .compute (RA.mono hstep) (RB.mono hstep) ih
  | symm H ih => exact .symm ih

/-- The original general singleton code with a recovered-carrier family guard and an
existential source realization. Its generated output is unchanged. -/
def CarrierRecoveredSingletonPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (e out : ProofShape) : Prop :=
  TypedSource Δ e ∧ SingletonPrimitiveWith (fun Δ => CarrierRecoveredCompare Step Δ true) Δ e out

/-- Primitive inclusion preserves all recursive recovered-carrier family guards. -/
theorem CarrierRecoveredSingletonPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : CarrierRecoveredSingletonPrimitive Step Δ e out) : CarrierRecoveredSingletonPrimitive Step' Δ e out :=
  ⟨H.1, H.2.mono (fun H => H.mono hstep)⟩

/-- Every computed singleton guard embeds as a base comparison. -/
theorem ComputedJointSingletonPrimitive.carrierRecovered
    (H : ComputedJointSingletonPrimitive Step Δ e out) :
    CarrierRecoveredSingletonPrimitive Step Δ e out :=
  ⟨H.1, H.2.mono (fun H => .base H)⟩
end ProofShape

/-- Finite layers of core computation, general singleton family guards, and
explicit-carrier Eq prefixes, using the enlarged family checker and the computed carrier checker. -/
def ErasedCarrierRecoveredStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedCarrierRecoveredStage D stage Δ a b ∨
      ProofShape.CarrierRecoveredSingletonPrimitive (ErasedCarrierRecoveredStage D stage) Δ a b ∨
      ProofShape.ComputedJointPrefixPrimitive (ErasedCarrierRecoveredStage D stage) Δ a b

/-- Every recovered-carrier stage descends through arbitrary inserted binder blocks. -/
theorem erased_carrier_recovered_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedCarrierRecoveredStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_carrier_recovered_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_computed_joint_prefix_descent heq ih hΓ hΓ' W ht H

/-- Existing computed joint computations embed without increasing their finite stage. -/
theorem erased_computed_into_carrier_recovered : ∀ stage {Δ a b},
    ErasedComputedJointStage D stage Δ a b → ErasedCarrierRecoveredStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.carrierRecovered.mono ih))
    · exact .inr (.inr (H.mono ih))

/-- Increasing a bound preserves endpoints and contexts. -/
theorem erased_carrier_recovered_stage_mono (hle : stage ≤ later) {Δ a b}
    (H : ErasedCarrierRecoveredStage D stage Δ a b) : ErasedCarrierRecoveredStage D later Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- The enlarged checker does not add reductions at neutral variable heads. -/
theorem erased_carrier_recovered_stage_head : ∀ stage {Δ a b},
    ErasedCarrierRecoveredStage D stage Δ a b → ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact ih H
    · exact H.2.head
    · exact H.head

/-- Every recovered-carrier primitive has exact original registered-prefix replay. -/
theorem erased_carrier_recovered_stage_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedCarrierRecoveredStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ e T out hΓ ht H
    obtain ⟨e', HR, HE⟩ := erased_iota_replay hs hΓ ht H
    exact ⟨e', .base HR, HE⟩
  | succ stage ih =>
    intro Γ e T out hΓ ht H
    rcases H with H | H | H
    · exact ih hΓ ht H
    · exact erased_singleton_with_replay heq
        (erased_carrier_recovered_family_descent (erased_carrier_recovered_stage_descent heq hs stage)) hΓ ht H.2
    · exact erased_computed_joint_prefix_replay heq hs
        (erased_carrier_recovered_stage_descent heq hs stage) hregistry hΓ ht H

/-- Compatible recovered-carrier computation retains an actual typed original path. -/
theorem proofErase_carrier_recovered_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧ proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_carrier_recovered_stage_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- A joint carrier guard enables the typed Eq prefix at the next stage. -/
theorem proofErase_carrier_recovered_prefix_stage_forward (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.ComputedJointCarrierGuard (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedCarrierRecoveredStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_computed_joint_prefix_forward heq (erased_carrier_recovered_stage_descent heq hs stage)
    hΓ ht HC).mono (fun H => .inr (.inr H))

/-- A checked generated prefix with a scoped family certificate computes in the
general raw primitive relation. Proof-valued whole sources give identity. -/
theorem proofErase_carrier_recovered_general_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.CarrierRecoveredCompare (ErasedCarrierRecoveredStage D stage) Δ true))
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ErasedCarrierRecoveredStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const data.name levels) args)) (proofErase Γ program.rhs) := by
  by_cases hp : IsProof Γ (mkApps (.const data.name levels) args)
  · rw [proofErase_eq_proof.2 hp,
      proofErase_eq_proof.2 ((isProof_congr hΓ (HC.defeq henv hΓ)).1 hp)]
    exact .refl
  let C : SingletonPrefixCode := ⟨data, levels, args.length, recType,
    program.equation, program.equationBody, S, E⟩
  obtain ⟨_, _, _, _, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  have V : C.Valid := ⟨hreg, H, hl, hz, hw, hrec, heqn, hbody, hS, hE, args, program, rfl, hg⟩
  have ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args) := ⟨_, HC.source_typed⟩
  have HE := proofErase_const_spine hΓ HC.source_typed hp
  have HT : ProofShape.TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const data.name levels) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, HC.source_typed, HE⟩
  rw [HE, V.output_eq heq hΓ hg HC hp]
  exact .base (.inr (.inl ⟨HT, .intro V (by simp only [List.length_map, C])
    (V.telescope_eq hΓ hg ht) ((V.guardWith_iff heq hΓ hg ht).2 HG)⟩))

/-- The union of all finite recovered-carrier stages. -/
def ErasedCarrierRecoveredUnion (D : PureObservation.Definitions) :=
  ProofShape.ScopedStageUnion (ErasedCarrierRecoveredStage D)

/-- Every original computed joint primitive embeds into the enlarged finite-stage union. -/
theorem erased_computed_union_into_carrier_recovered (H : ErasedComputedJointUnion D Δ a b) :
    ErasedCarrierRecoveredUnion D Δ a b := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_computed_into_carrier_recovered stage H⟩

end Lean4Lean.VEnv.Strengthening
