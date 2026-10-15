import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationComparison

/-! # Finite bounds for contextual certificates over a union of stages

Each primitive may initially choose its own stage. Finitary certificate
construction, including bounded structure-field families, collects those choices
into one bound. No normalization or recovery completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean Params

/-- Allow each primitive occurrence to choose a finite stage independently. -/
def ScopedStageUnion (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop := ∃ stage, Stages stage Δ a b

/-- Primitive stages grow without changing their contexts or endpoints. -/
def ScopedStagesMonotone (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {stage later}, stage ≤ later → ∀ {Δ a b}, Stages stage Δ a b → Stages later Δ a b

private theorem finite_uniform_bound {P : Nat → Nat → Prop}
    (hmono : ∀ {i n m}, n ≤ m → P i n → P i m)
    (H : ∀ i, i < count → ∃ stage, P i stage) :
    ∃ stage, ∀ i, i < count → P i stage := by
  induction count with
  | zero => exact ⟨0, by intro i hi; omega⟩
  | succ count ih =>
    obtain ⟨n, hn⟩ := ih (fun i hi => H i (by omega))
    obtain ⟨m, hm⟩ := H count (by omega)
    refine ⟨max n m, ?_⟩
    intro i hi
    by_cases h : i < count
    · exact hmono (Nat.le_max_left _ _) (hn i h)
    · have E : i = count := by omega
      subst i
      exact hmono (Nat.le_max_right _ _) hm

/-- A compatible computation over the union has one finite stage bound. -/
theorem ScopedCompute.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : ScopedCompute (ScopedStageUnion Stages) Δ a b) :
    ∃ stage, ScopedCompute (Stages stage) Δ a b := by
  induction R with
  | base H => obtain ⟨stage, H⟩ := H; exact ⟨stage, .base H⟩
  | beta H => exact ⟨0, .beta H⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .trans (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .app (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | proj _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .proj H⟩
  | lam _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .lam (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | forallE _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .forallE (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩

/-- Taking the union inside compatible computation adds no infinite paths. -/
theorem scoped_compute_union_iff (hmono : ScopedStagesMonotone Stages) :
    ScopedCompute (ScopedStageUnion Stages) Δ a b ↔ ∃ stage, ScopedCompute (Stages stage) Δ a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

variable [Params]

/-- Contextual recovery over the union also has a single finite bound,
including its computation under binders and closed projection recipes. -/
theorem ScopedTypeRecovery.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : ScopedTypeRecovery (ScopedStageUnion Stages) Δ e T) :
    ∃ stage, ScopedTypeRecovery (Stages stage) Δ e T := by
  induction R with
  | bvar => exact ⟨0, .bvar⟩
  | sort H => exact ⟨0, .sort H⟩
  | const hc hw hn => exact ⟨0, .const hc hw hn⟩
  | lam _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .lam H⟩
  | app _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .app H⟩
  | forallE _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .forallE (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | proj hi HT hj hlen _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .proj hi HT hj hlen H⟩
  | convert _ RC ih =>
    obtain ⟨n, H⟩ := ih; obtain ⟨m, K⟩ := RC.finite_stage hmono
    exact ⟨max n m, .convert (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩

/-- Union recovery is exactly existential finite-stage recovery. -/
theorem scoped_recovery_union_iff (hmono : ScopedStagesMonotone Stages) :
    ScopedTypeRecovery (ScopedStageUnion Stages) Δ e T ↔ ∃ stage, ScopedTypeRecovery (Stages stage) Δ e T :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

/-- Scoped comparisons have finite stage bounds even when retained fields
initially choose different bounds. Proof-marker fields require no certificate. -/
theorem ScopedCompare.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : ScopedCompare (ScopedStageUnion Stages) Δ mode a b) :
    ∃ stage, ScopedCompare (Stages stage) Δ mode a b := by
  induction R with
  | leaf H => exact ⟨0, .leaf H⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .app (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
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
    obtain ⟨stage, HB⟩ := finite_uniform_bound
      (P := fun i stage => ∀ h : i < fields.length, fields[i] ≠ .proof →
        ScopedCompare (Stages stage) Δ true fields[i] (.proj family i major))
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

/-- Explicit carrier guards have finite bounds, including recursive fields,
fresh function applications, and separate carrier/endpoint computations. -/
theorem StructureCarrierGuard.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : StructureCarrierGuard (ScopedStageUnion Stages) Δ A a b) :
    ∃ stage, StructureCarrierGuard (Stages stage) Δ A a b := by
  induction R with
  | @intro family info ls Δ a b ps hi hx hp hadm H =>
    obtain ⟨stage, HB⟩ := finite_uniform_bound (count := info.numFields)
      (P := fun i stage => StructureReplay.ProofField env univs info ls i ∨
        ScopedCompare (Stages stage) Δ true (.proj family i a) (.proj family i b))
      (fun hle H => H.imp id (fun H => H.mono (hmono hle))) (fun i hi => by
        rcases H i hi with HP | HC
        · exact ⟨0, .inl HP⟩
        · obtain ⟨stage, HC⟩ := HC.finite_stage hmono
          exact ⟨stage, .inr HC⟩)
    exact ⟨stage, .intro hi hx hp hadm HB⟩
  | checked H => obtain ⟨stage, H⟩ := H.finite_stage hmono; exact ⟨stage, .checked H⟩
  | subsingleton H => exact ⟨0, .subsingleton H⟩
  | function S _ ih => obtain ⟨stage, H⟩ := ih; exact ⟨stage, .function S H⟩
  | symm _ ih => obtain ⟨stage, H⟩ := ih; exact ⟨stage, .symm H⟩
  | compute RC _ ih =>
    obtain ⟨n, H⟩ := ih; obtain ⟨m, C⟩ := RC.finite_stage hmono
    exact ⟨max n m, .compute (C.mono (hmono (Nat.le_max_right _ _))) (H.mono (hmono (Nat.le_max_left _ _)))⟩
  | reduce RA RB _ ih =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, A⟩ := RA.finite_stage hmono; obtain ⟨k, B⟩ := RB.finite_stage hmono
    refine ⟨max n (max m k), .reduce (A.mono (hmono ?_)) (B.mono (hmono ?_)) (H.mono (hmono ?_))⟩ <;> omega
  | @nested family info ls doms result Δ ps a b hi hx hp hadm HT H ih =>
    classical
    obtain ⟨stage, HB⟩ := finite_uniform_bound (count := info.numFields)
      (P := fun i stage => ∀ hj : i < info.numFields, ¬ StructureReplay.ProofField env univs info ls i →
        StructureCarrierGuard (Stages stage) Δ
          (projectionType family info doms i (by have := HT.numFields; omega) ps a)
          (.proj family i a) (.proj family i b))
      (fun hle H hj hn => (H hj hn).mono (hmono hle)) (fun i hj => by
        by_cases hn : StructureReplay.ProofField env univs info ls i
        · exact ⟨0, fun _ H => (H hn).elim⟩
        · obtain ⟨stage, HC⟩ := ih i hj hn
          exact ⟨stage, fun _ _ => HC⟩)
    exact ⟨stage, .nested hi hx hp hadm HT (fun i hj hn => HB i hj hj hn)⟩

/-- Enlarged recursive comparison, including recovered application domains,
uses only finitely many stages. The recovered Pi and its carrier guard share
the output bound with the recursive function comparison. -/
theorem ApplicationCompare.finite_stage (hmono : ScopedStagesMonotone Stages)
    (R : ApplicationCompare (ScopedStageUnion Stages) Δ mode a b) :
    ∃ stage, ApplicationCompare (Stages stage) Δ mode a b := by
  induction R with
  | leaf H => exact ⟨0, .leaf H⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .app (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | appCarrier R _ HX ih =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, R⟩ := R.finite_stage hmono
    obtain ⟨k, HX⟩ := HX.finite_stage hmono
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
    obtain ⟨stage, HB⟩ := finite_uniform_bound
      (P := fun i stage => ∀ h : i < fields.length, fields[i] ≠ .proof →
        ApplicationCompare (Stages stage) Δ true fields[i] (.proj family i major))
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

/-- A union scoped comparison is exactly a comparison at some finite stage. -/
theorem scoped_compare_union_iff (hmono : ScopedStagesMonotone Stages) :
    ScopedCompare (ScopedStageUnion Stages) Δ mode a b ↔ ∃ stage, ScopedCompare (Stages stage) Δ mode a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

/-- A union carrier guard is exactly a guard at some finite stage. -/
theorem carrier_guard_union_iff (hmono : ScopedStagesMonotone Stages) :
    StructureCarrierGuard (ScopedStageUnion Stages) Δ A a b ↔ ∃ stage, StructureCarrierGuard (Stages stage) Δ A a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

/-- Union application checking introduces no infinite comparison certificates. -/
theorem application_compare_union_iff (hmono : ScopedStagesMonotone Stages) :
    ApplicationCompare (ScopedStageUnion Stages) Δ mode a b ↔ ∃ stage, ApplicationCompare (Stages stage) Δ mode a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
