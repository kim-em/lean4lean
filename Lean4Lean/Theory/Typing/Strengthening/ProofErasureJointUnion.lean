import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageUnion

/-! # Finite bounds and the closed union of joint checking stages

The single induction includes arbitrarily many alternations between comparison
and carrier checking. Every union certificate has a finite bound, so general
singleton and Eq guards over the union still belong at finite successor stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private ProofShape.finite_uniform_bound from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageUnion
variable [Params]
namespace ProofShape

/-- Enlarged recursive comparison, including recovered application domains,
uses only finitely many stages. The recovered Pi and its carrier guard share
the output bound with the recursive function comparison. -/
theorem JointCheck.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : JointCheck (ScopedStageUnion Stages) Δ kind a b) :
    ∃ stage, JointCheck (Stages stage) Δ kind a b := by
  induction R with
  | leaf H => exact ⟨0, .leaf H⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .app (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | appCarrier R _ _ ih ihx =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, R⟩ := R.finite_stage hmono
    obtain ⟨k, HX⟩ := ihx
    refine ⟨max n (max m k), .appCarrier (R.mono (hmono ?_))
      (H.mono (hmono ?_)) (HX.mono (hmono ?_))⟩ <;> omega
  | proj _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .proj H⟩
  | lam _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .lam (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | forallE _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .forallE (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | lamSorted S S' _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .lamSorted S S' (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | forallSorted S S' _ T T' _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .forallSorted S S' (H.mono (hmono (Nat.le_max_left _ _))) T T'
      (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | lamCommon _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .lamCommon H⟩
  | etaBodyL S _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .etaBodyL S H⟩
  | etaBodyR S _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .etaBodyR S H⟩
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm H ih =>
    classical
    obtain ⟨stage, HB⟩ := ProofShape.finite_uniform_bound
      (P := fun i stage => ∀ h : i < fields.length, fields[i] ≠ .proof →
        JointCheck (Stages stage) Δ (.compare true) fields[i] (.proj family i major))
      (fun hle H h hn => (H h hn).mono (hmono hle)) (fun i hi => by
        by_cases hn : fields[i] ≠ .proof
        · obtain ⟨stage, HC⟩ := ih i hi hn
          exact ⟨stage, fun _ _ => HC⟩
        · exact ⟨0, fun _ H => (hn H).elim⟩)
    exact ⟨stage, .structFields hi hx hp hf hadm (fun i hi hn => HB i hi hi hn)⟩
  | etaLams _ Hη ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .etaLams H Hη⟩
  | compute RA RB _ ih =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, A⟩ := RA.finite_stage hmono
    obtain ⟨k, B⟩ := RB.finite_stage hmono
    refine ⟨max n (max m k), .compute (A.mono (hmono ?_)) (B.mono (hmono ?_)) (H.mono (hmono ?_))⟩ <;> omega
  | symm _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .symm H⟩

  | carrierChecked _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .carrierChecked H⟩
  | carrierSubsingleton H => exact ⟨0, .carrierSubsingleton H⟩
  | carrierFunction S _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .carrierFunction S H⟩
  | carrierSymm _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .carrierSymm H⟩
  | carrierCompute RC _ ih =>
    obtain ⟨n, H⟩ := ih; obtain ⟨m, C⟩ := RC.finite_stage hmono
    exact ⟨max n m, .carrierCompute (C.mono (hmono (Nat.le_max_right _ _)))
      (H.mono (hmono (Nat.le_max_left _ _)))⟩
  | carrierReduce RA RB _ ih =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, A⟩ := RA.finite_stage hmono; obtain ⟨k, B⟩ := RB.finite_stage hmono
    refine ⟨max n (max m k), .carrierReduce (A.mono (hmono ?_))
      (B.mono (hmono ?_)) (H.mono (hmono ?_))⟩ <;> omega
  | @carrierIntro family info ls Δ a b ps hi hx hp hadm H ih =>
    classical
    obtain ⟨stage, HB⟩ := ProofShape.finite_uniform_bound (count := info.numFields)
      (P := fun i stage => ∀ hj : i < info.numFields, ¬ StructureReplay.ProofField env univs info ls i →
        JointCompare (Stages stage) Δ true (.proj family i a) (.proj family i b))
      (fun hle H hj hn => (H hj hn).mono (hmono hle)) (fun i hj => by
        by_cases hn : StructureReplay.ProofField env univs info ls i
        · exact ⟨0, fun _ H => (H hn).elim⟩
        · obtain ⟨stage, HC⟩ := ih i hj hn
          exact ⟨stage, fun _ _ => HC⟩)
    exact ⟨stage, .carrierIntro hi hx hp hadm (fun i hj hn => HB i hj hj hn)⟩
  | @carrierNested family info ls doms result Δ ps a b hi hx hp hadm HT H ih =>
    classical
    obtain ⟨stage, HB⟩ := ProofShape.finite_uniform_bound (count := info.numFields)
      (P := fun i stage => ∀ hj : i < info.numFields, ¬ StructureReplay.ProofField env univs info ls i →
        JointCarrierGuard (Stages stage) Δ
          (projectionType family info doms i (by have := HT.numFields; omega) ps a)
          (.proj family i a) (.proj family i b))
      (fun hle H hj hn => (H hj hn).mono (hmono hle)) (fun i hj => by
        by_cases hn : StructureReplay.ProofField env univs info ls i
        · exact ⟨0, fun _ H => (H hn).elim⟩
        · obtain ⟨stage, HC⟩ := ih i hj hn
          exact ⟨stage, fun _ _ => HC⟩)
    exact ⟨stage, .carrierNested hi hx hp hadm HT (fun i hj hn => HB i hj hj hn)⟩

/-- Both views of the joint grammar have exactly the existential finite-stage
meaning. No infinitary comparison/carrier recursion is added by a union. -/
theorem joint_check_union_iff (hmono : ScopedStagesMonotone Stages) :
    JointCheck (ScopedStageUnion Stages) Δ kind a b ↔ ∃ stage, JointCheck (Stages stage) Δ kind a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

/-- General joint singleton guards over a union choose one finite stage;
the source realization and exact generated program do not change. -/
theorem JointSingletonPrimitive.finite_stage (hmono : ScopedStagesMonotone Stages)
    (H : JointSingletonPrimitive (ScopedStageUnion Stages) Δ a b) :
    ∃ stage, JointSingletonPrimitive (Stages stage) Δ a b := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨stage, HG⟩ := JointCheck.finite_stage hmono HG
    exact ⟨stage, HT, .intro V ha hcalc HG⟩
end ProofShape

/-- All finite joint stages, allowing independent bounds at primitive occurrences. -/
def ErasedJointUnion (D : PureObservation.Definitions) := ScopedStageUnion (ErasedJointStage D)

/-- The union is closed under its own general singleton and joint Eq guards. -/
theorem erased_joint_union_iff :
    ErasedJointUnion D Δ a b ↔ ErasedIotaPrimitive D a b ∨
      JointSingletonPrimitive (ErasedJointUnion D) Δ a b ∨ JointPrefixPrimitive (ErasedJointUnion D) Δ a b := by
  constructor
  · rintro ⟨stage, H⟩
    induction stage with
    | zero => exact .inl H
    | succ stage ih =>
      rcases H with H | H | H
      · exact ih H
      · exact .inr (.inl (H.mono (fun H => ⟨stage, H⟩)))
      · exact .inr (.inr (H.mono (fun H => ⟨stage, H⟩)))
  · intro H
    rcases H with H | H | H
    · exact ⟨0, H⟩
    · obtain ⟨stage, H⟩ := H.finite_stage erased_joint_stage_mono
      exact ⟨stage + 1, .inr (.inl H)⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
        exact ⟨stage + 1, .inr (.inr (.intro HC))⟩

/-- The closed joint union retains arbitrary-block source-typed descent. -/
theorem erased_joint_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedJointUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_joint_stage_descent heq hs stage hΓ hΓ' W ht H

/-- Union primitives still only contract constant/projection heads. -/
theorem erased_joint_union_head (H : ErasedJointUnion D Δ a b) : PrimitiveHead a := by
  obtain ⟨stage, H⟩ := H
  exact erased_joint_stage_head stage H

/-- Every union primitive replays through an actual original prefix computation. -/
theorem erased_joint_union_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ErasedJointUnion D) := by
  intro Γ e T out hΓ ht H
  obtain ⟨stage, H⟩ := H
  exact erased_joint_stage_replay heq hs hregistry stage hΓ ht H

end Lean4Lean.VEnv.Strengthening
