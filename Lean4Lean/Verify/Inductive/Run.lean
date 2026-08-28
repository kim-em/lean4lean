import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.Nested.CompilationAssembly
import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.Nested.FreshTraceLemmas
import Lean4Lean.Verify.Inductive.Nested.ConcreteBoundary
import Lean4Lean.Verify.Inductive.Nested.ExpansionProjection
import Lean4Lean.Verify.Inductive.Nested.FormationEvidence
import Lean4Lean.Verify.Inductive.Nested.SourceMetadata
import Lean4Lean.Verify.Inductive.Recursor.TelescopeRestriction
import Lean4Lean.Verify.Inductive.Nested.CanonicalSuffixSemantics
import Lean4Lean.Verify.Inductive.Nested.OriginalHeaderSeedRebase
import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilySemantics
import Lean4Lean.Verify.Inductive.Nested.CanonicalFamilySuffix
import Lean4Lean.Verify.Inductive.Nested.PrimaryEquations
import Lean4Lean.Verify.Inductive.Nested.ProductionOrigins
import Lean4Lean.Verify.Inductive.Nested.EquationRestoration
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationTranslation
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRhs
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationNodeSemantics
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIota
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuarded
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationTyping
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIotaStructural
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationList
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFreeness
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSeeds
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSeedAlignment
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedAtomic
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorNames
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedFreshness
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardSeeds
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorFree
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFieldApps
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecCall
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedOrdinary
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSpines
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorSpines
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationMinor
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationLambdas
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIotaAutomatic
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationBatch
import Lean4Lean.Verify.Inductive.Primitive
import Lean4Lean.Verify.Inductive.PrimitiveEvidence
import Lean4Lean.Verify.Inductive.PrimitiveBootstrap
import Lean4Lean.Verify.Inductive.Header.SourceTelescope
import Lean4Lean.Verify.Inductive.TypeAnnotations
import Lean4Lean.Verify.Inductive.Run.EqCanonical

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
