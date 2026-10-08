import Lean4Lean.Verify.Inductive.CompletedRecursorPhases
import Lean4Lean.Verify.Inductive.CompletedConstructorPhases
import Lean4Lean.Verify.Inductive.ConstructorBoundary
import Lean4Lean.Verify.Inductive.Header.SingletonElimination
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterRawShape
import Lean4Lean.Theory.Inductive.SignatureLemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The completed run fixes both the source signature and its universe
instance. Generation and concrete metadata must use this same choice. -/
noncomputable def CompletedRecursorPhasesResult.canonicalGeneration
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    InductiveSignature.Instance H.toCompletedRecursorConstruction.generationSignature :=
  H.toCompletedRecursorConstruction.generationInstance

/-- Admissibility belongs to the same consumed signature selected before
installation, including the actual singleton decision and universe policy. -/
theorem CompletedRecursorPhasesResult.canonicalGeneration_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.canonicalGeneration.Admissible R.headerVEnv :=
  H.toCompletedRecursorConstruction.consumedGeneration.admissible

end VerifyInductive
end Lean4Lean
