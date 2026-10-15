import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPrefix
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveSingletonStages

/-! # Computation guarded by mutually recursive comparison and carriers

Every singleton family comparison and every specialized Eq carrier may use the
joint grammar. Recovery and computation use the preceding stage. All earlier
recursive-singleton stages embed at their original bounds.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Joint comparison supplies the generic family descent requirement. -/
theorem erased_joint_family_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedFamilyDescent (fun Δ => ProofShape.JointCompare Step Δ true) := by
  intro Γ Γ' n k P Q hΓ hΓ' W hP hQ HC
  exact ((proofErase_joint_compare_descend hstep hΓ hΓ' W rfl hP hQ HC).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hΓ hP

namespace ProofShape
/-- The original general singleton code with a joint family guard and an
existential source realization. Its generated output is unchanged. -/
def JointSingletonPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (e out : ProofShape) : Prop :=
  TypedSource Δ e ∧ SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) Δ e out

/-- Primitive inclusion preserves all recursive joint family guards. -/
theorem JointSingletonPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : JointSingletonPrimitive Step Δ e out) : JointSingletonPrimitive Step' Δ e out :=
  ⟨H.1, H.2.mono (fun H => H.mono hstep)⟩

/-- Previous recursive application guards embed without changing code or bounds. -/
theorem ApplicationSingletonPrimitive.joint (H : ApplicationSingletonPrimitive Step Δ e out) :
    JointSingletonPrimitive Step Δ e out := ⟨H.1, H.2.mono (fun H => H.joint)⟩
end ProofShape

/-- Finite layers of core computation, general singleton family guards, and
explicit-carrier Eq prefixes, all using the joint recursive checker. -/
def ErasedJointStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedJointStage D stage Δ a b ∨
      ProofShape.JointSingletonPrimitive (ErasedJointStage D stage) Δ a b ∨
      ProofShape.JointPrefixPrimitive (ErasedJointStage D stage) Δ a b

/-- Every joint stage descends through arbitrary inserted binder blocks. -/
theorem erased_joint_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedJointStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_joint_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_joint_prefix_descent heq ih hΓ hΓ' W ht H

/-- All preceding recursive-singleton stages embed at exactly the same bound. -/
theorem erased_recursive_singleton_into_joint : ∀ stage {Δ a b},
    ErasedRecursiveSingletonStage D stage Δ a b → ErasedJointStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.joint.mono ih))
    · exact .inr (.inr (H.joint.mono ih))
    · exact .inr (.inr (H.joint.mono ih))

/-- Increasing a bound preserves endpoints and contexts. -/
theorem erased_joint_stage_mono (hle : stage ≤ later) {Δ a b}
    (H : ErasedJointStage D stage Δ a b) : ErasedJointStage D later Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- The joint checker does not add reductions at neutral variable heads. -/
theorem erased_joint_stage_head : ∀ stage {Δ a b},
    ErasedJointStage D stage Δ a b → ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact ih H
    · exact H.2.head
    · exact H.head

/-- Every joint primitive has exact original registered-prefix replay. -/
theorem erased_joint_stage_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedJointStage D stage) := by
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
        (erased_joint_family_descent (erased_joint_stage_descent heq hs stage)) hΓ ht H.2
    · exact erased_joint_prefix_replay heq hs
        (erased_joint_stage_descent heq hs stage) hregistry hΓ ht H

/-- Compatible joint-stage computation retains an actual typed original path. -/
theorem proofErase_joint_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧ proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_joint_stage_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- A joint carrier guard enables the typed Eq prefix at the next stage. -/
theorem proofErase_joint_prefix_stage_forward (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_joint_prefix_forward heq (erased_joint_stage_descent heq hs stage)
    hΓ ht HC).mono (fun H => .inr (.inr H))

/-- A checked generated prefix with a scoped family certificate computes in the
general raw primitive relation. Proof-valued whole sources give identity. -/
theorem proofErase_joint_general_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare (ErasedJointStage D stage) Δ true))
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
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

end Lean4Lean.VEnv.Strengthening
