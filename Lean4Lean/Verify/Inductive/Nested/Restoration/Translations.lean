import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorTranslations
import Lean4Lean.Verify.Inductive.Nested.Lowering.Recognition
import Lean4Lean.Verify.Inductive.Recursor.Entries.Metadata

/-! Translations of the executable nested restoration folds: the source family
translations (`SourceFamilyTranslations`: header, constructors and source recursor of
each source family) and the auxiliary recursor fold (`AuxiliaryRecursorRuleBatches`),
the restored block `restoredBlock`, and the auxiliary-constructor freshness
consequence of installation. Shared lookup and mutual-header effects live in
`Install/Metadata.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One executable auxiliary recursor restoration step: the translated
recursor constant and the abstract rule batch of the step, of the restored
length. The record fixes no equation syntax; the rules are fixed by the
compilation of the nested installation. -/
structure AuxiliaryRecursorRuleBatch
    (safety : DefinitionSafety) (trEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv) where
  recursor : VConstVal
  rules : List VDefEq
  translated : TrConstVal safety trEnv
    (.recInfo Hstep.restored.newInfo) recursor
  rulesLength : rules.length = Hstep.restored.newInfo.rules.length

/-- Translation, typing and shape of one restored source recursor. -/
structure SourceRecursorTranslation
    (decl : VInductDecl) (owner : VInductiveType)
    (safety : DefinitionSafety)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (sourceVEnv : VEnv) where
  recursor : VConstVal
  safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type
  name : recursor.name = Hstep.restored.newRecName
  wf : recursor.toVConstant.WF sourceVEnv
  shape : Nonempty (decl.NestedRecursorShape owner recursor)

/-- The abstract source recursor of one source family. It mentions neither the
lowered declaration nor any executable restoration step: it is the abstract
specification which the executable recursor construction must refine. -/
structure SourceRecursorSpec
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (canonicalEnv : VEnv) where
  recursor : VConstVal
  name : recursor.name = sourceDecl.recursorName owner
  isType : canonicalEnv.IsType recursor.uvars [] recursor.type
  shape : Nonempty (sourceDecl.NestedRecursorShape owner recursor)

/-- Executable-to-specification refinement for a restored source recursor.
The source recursor is fixed by `SourceRecursorSpec`; this record
states that the executable restoration step has exactly its universe arity and
translates its restored telescope to exactly its abstract type. -/
structure SourceRecursorRefinement
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) : Prop where
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type

/-- One abstract source recursor translating a particular restored executable
recursor. The equality field ties the source specification and the refinement
to the same constant. -/
structure TrSourceRecursor
    (sourceDecl : VInductDecl) (sourceOwner : VInductiveType)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) where
  source : SourceRecursorSpec sourceDecl sourceOwner canonicalEnv
  recursor_eq : source.recursor = recursor
  refinement : SourceRecursorRefinement Hstep canonicalEnv recursor

/-- Source translations of the families along the source-family restoration fold. -/
inductive SourceFamilyTranslations
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety)
    (sourceVEnv envTypes envCtors : VEnv) :
    ∀ {types sourceProdEnv targetProdEnv},
      FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors
        (FoldSteps.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : SourceRecursorTranslation decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : SourceFamilyTranslations decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors (.cons Hstep Htail) (owner :: owners)
        (Hrecursor.recursor :: recursors)

/-- The source translations for one executable family restoration step: header,
constructors and source recursor. Bundling the fields keeps the mutual fold
independent of how each of them is proved. -/
structure SourceFamilyTranslation
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety) (sourceVEnv envTypes envCtors : VEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  owner : VInductiveType
  header : TrSourceConst sourceVEnv lparams indType.name indType.type
    owner.toVConstVal
  constructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
    Hstep.oldInfo.ctors Hstep.restored.headerEnv
      Hstep.restored.constructorEnv indType.ctors owner.ctors
  recursor : SourceRecursorTranslation decl owner safety
    Hstep.restored.recursor envCtors

theorem SourceFamilyTranslations.types
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (TrInductiveType sourceVEnv envTypes lparams)
      sourceTypes owners := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hheader, Hconstructors.forall₂⟩ ih

/-- The source declaration translation `TrInductDeclCore`, from the source family
translations. The restoration fold fixes all pointwise source/target
correspondences; only the abstract header and constructor environments and the
declaration metadata are supplied separately. -/
theorem SourceFamilyTranslations.core
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners)
    (huvars : decl.uvars = lparams.length)
    (hnparams : decl.nparams = nparams)
    (hisUnsafe : decl.isUnsafe = isUnsafe)
    (htypesAdded : sourceVEnv.addConstVals decl.typeConstants = some envTypes)
    {envCtors' : VEnv}
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors') :
    TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe decl
      envTypes envCtors' := by
  refine {
    uvars := huvars
    nparams := hnparams
    isUnsafe := hisUnsafe
    typesAdded := htypesAdded
    ctorsAdded := hctorsAdded
    types := ?_ }
  rw [htypes]
  exact H.types

/-- The restored block of a nested declaration: the source declaration's
families, constructors and projection entries, the source recursors followed by
the auxiliary recursors, and their rules in the same order. -/
def restoredBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  projections := decl.projectionEntries
  recursors := primaryRecursors ++ auxiliaryRecursors
  rules := primaryRules ++ auxiliaryRules

end VerifyInductive
end Lean4Lean
