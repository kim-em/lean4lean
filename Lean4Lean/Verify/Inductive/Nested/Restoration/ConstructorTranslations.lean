import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One source constructor paired with the exact operational restoration
step that installs it.  Source translation is stated in the canonical
post-header environment, not the production interleaved environment. -/
structure RestoredSourceConstructorSemantics
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (source : Constructor) where
  constructor : VConstVal
  sourceTranslation : TrSourceConst canonicalEnv lparams source.name
    source.type constructor
  restoredTranslation : TrConstVal safety canonicalEnv
    (.ctorInfo Hstep.restored.newInfo) constructor

/-- Positional source-constructor semantics for the exact constructor
restoration fold of one family. -/
inductive RestoredSourceConstructorTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment)
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv) :
    List Name → Environment → Environment →
      List Constructor → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        [] sourceProdEnv sourceProdEnv [] []
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Hsemantic : RestoredSourceConstructorSemantics lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        names middleProdEnv targetProdEnv sources constructors) :
      RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        (ctorName :: names) sourceProdEnv targetProdEnv (source :: sources)
        (Hsemantic.constructor :: constructors)

theorem RestoredSourceConstructorTrace.forall₂
    (H : RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv names
      sourceProdEnv targetProdEnv sources constructors) :
    List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Hsemantic Hrest ih =>
    exact .cons Hsemantic.sourceTranslation ih


end VerifyInductive
end Lean4Lean
