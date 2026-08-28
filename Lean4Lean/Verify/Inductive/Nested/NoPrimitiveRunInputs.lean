import Lean4Lean.Verify.Inductive.Run.SemanticRun
import Lean4Lean.Verify.Inductive.Nested.EndToEnd

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Semantic run inputs for the non-primitive nested path

The canonical nested branch runs `AddInductive` with primitive declarations
disabled.  Consequently all three production-name freshness fields in
`SemanticRunVerificationInputs` are unreachable.
-/

/-- Construct the complete semantic-run input package when the executable
context has primitive declarations disabled. -/
theorem SemanticRunVerificationInputs.ofNoPrimitive
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {nparams depth numNested : Nat} {indTypes : Array InductiveType}
    {isUnsafe : Bool} {Hc : ContextWF c}
    (hallow : c.allowPrimitive = false)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat) :
    SemanticRunVerificationInputs c stats nparams depth numNested indTypes
      isUnsafe Hc where
  freshTypes htrue := by simp [hallow] at htrue
  freshConstructors htrue := by simp [hallow] at htrue
  loopUArgsReplay := hloopUArgsReplay
  freshRecursors htrue := by simp [hallow] at htrue

/-- A successful lowering trace necessarily began with a nonempty mutual
source block; this is fixed by the executable's first pattern match. -/
theorem NestedLoweringResult.sourceNonempty
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    sourceTypes ≠ [] := by
  rcases H with ⟨_finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, _tail, _paramsState, _lctx, _params, hsource, _⟩
  rw [hsource]
  simp

/-- The lowered declaration passed to `AddInductive.run` is nonempty whenever
the exact lowering execution succeeded. -/
theorem NestedLoweringResult.resultTypesSizePos
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    0 < result.types.toArray.size := by
  have hsource := H.sourceNonempty
  have hsourcePos : 0 < sourceTypes.length := by
    cases sourceTypes with
    | nil => contradiction
    | cons => simp
  have hresultPos : 0 < result.types.length := by
    have hle := H.sourceTypes_length_le
    omega
  simpa using hresultPos

/-- The safety selected by the public inductive entry point is never the
partial-definition mode rejected by recursor generation. -/
theorem inductiveSafety_notPartial (isUnsafe : Bool) :
    (if isUnsafe then DefinitionSafety.unsafe else .safe) ≠
      DefinitionSafety.partial := by
  cases isUnsafe <;> decide

end VerifyInductive
end Lean4Lean
