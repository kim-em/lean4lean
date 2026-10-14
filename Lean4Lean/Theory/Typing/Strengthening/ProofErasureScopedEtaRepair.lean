import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCoverage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveEtaBoundary
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # Recursive eta now feeds finite prefix computation -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private RecursiveEtaBoundary.functionType_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveEtaBoundary
variable [Params]
namespace RecursiveEtaBoundary

/-- The typed recursive-eta witness has a scoped certificate even before any
primitive computation; this holds for every scoped computational relation. -/
theorem scoped_guard : ProofShape.ScopedCompare Step (proofEraseCtx ctx) true
    (proofErase ctx long) (proofErase ctx short) := .base contextual

/-- The new guards strictly cover the typed recursive-eta witness omitted by
every finite earlier raw K/prefix stage. -/
theorem scoped_beyond_all_raw_stages (D : PureObservation.Definitions) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D 0) (proofEraseCtx ctx) true
      (proofErase ctx long) (proofErase ctx short) ∧
    ∀ stage mode, ¬ ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) mode
      (proofErase ctx long) (proofErase ctx short) :=
  ⟨scoped_guard, fun _ _ => erased_stages_not_compare⟩

/-- A prefix containing the nested-eta endpoints now unfolds at stage one.
Its guard uses only the checked original witness's contextual eta certificate. -/
theorem scoped_prefix :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D 1) (proofEraseCtx ctx)
      (ProofShape.eqRecBeforeMajor v w α rawLong M m rawShort)
      (.lam (ProofShape.eqProofType w α rawLong rawShort) (m.liftN 1)) := by
  apply ProofShape.ScopedCompute.base
  apply Or.inr
  apply ProofShape.ScopedPrefixKPrimitive.intro
  simpa only [erasures.1, erasures.2] using
    (scoped_guard (Step := ErasedScopedPrefixStage D 0))

/-- For any typed original prefix with these endpoints, the stage-one path has
the exact erasure of its canonical original lambda as target. -/
theorem typed_scoped_prefix (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (ht : env.HasType univs ctx (eqRecBeforeMajor v w α long M m short) T) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D 1) (proofEraseCtx ctx)
      (proofErase ctx (eqRecBeforeMajor v w α long M m short))
      (proofErase ctx (.lam (eqApp w α long short) m.lift)) :=
  proofErase_scoped_prefix_stage_forward heq hs ctx_wf ht scoped_guard

/-- A constant sort-valued motive for a concrete typed prefix example. -/
def testMotive : VExpr := constantEqMotive (.succ .zero) functionType long (.sort (.succ .zero))

/-- A concrete prefix whose endpoints require recursive eta in its guard. -/
def testPrefix : VExpr := eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero)
  functionType long testMotive (.sort .zero) short

/-- The concrete prefix is typed in the original well-formed witness context;
no equality-proof major needs to be supplied. -/
theorem testPrefix_typed (heq : env.HasCanonicalEq) :
    ∃ T, env.HasType univs ctx testPrefix T := by
  have hα := RecursiveEtaBoundary.functionType_typed (Γ := ctx)
  have hM := constantEqMotive_typed henv.ordered heq (by trivial) hα typings.1
    (HasType.sort (by trivial : (VLevel.succ .zero).WF univs))
  have HE := constantEqMotive_app henv heq (by trivial) ctx_wf hα typings.1
    (HasType.sort (by trivial : (VLevel.succ .zero).WF univs)) typings.1
    (HasType.eqReflApp heq (by trivial) hα typings.1)
  have hm := HE.symm.defeq (HasType.sort (by trivial : VLevel.zero.WF univs))
  exact ⟨_, eqRecBeforeMajor_typed heq (by trivial) (by trivial) hα typings.1 hM hm typings.2⟩

/-- The new stage executes an actual typed recursive-eta prefix, with an exact
original lambda target. This is a coverage repair, not full completeness. -/
theorem testPrefix_computes (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ T, env.HasType univs ctx testPrefix T ∧
      ProofShape.ScopedCompute (ErasedScopedPrefixStage D 1) (proofEraseCtx ctx)
        (proofErase ctx testPrefix)
        (proofErase ctx (.lam (eqApp (.succ .zero) functionType long short) (.sort .zero))) := by
  obtain ⟨T, ht⟩ := testPrefix_typed heq
  exact ⟨T, ht, typed_scoped_prefix heq hs ht⟩

end RecursiveEtaBoundary
end Lean4Lean.VEnv.Strengthening
