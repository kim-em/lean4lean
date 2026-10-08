import Lean4Lean.Verify.Inductive.Recursor.Construction
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.CanonicalParameterReplay
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMotiveGroup
import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorModel
import Lean4Lean.Verify.Inductive.ConsumedTranslation
import Lean4Lean.Verify.Inductive.Recursor.ConsumedGenerationAssembly
import Lean4Lean.Verify.Inductive.Recursor.ArgumentUniverses
import Lean4Lean.Verify.Inductive.Recursor.FamilyTypes

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Source identities and recursive choices for one consumed constructor.
The original first-pass traversal and hypothesis inputs remain available;
canonical binder syntax is selected from those actual consumed sources. -/
structure ConsumedConstructorOrigins
    (s : InductiveSignature) (S : RecInfoMinorTypeShape)
    (ctor : InductiveSignature.Constructor s.families.size) where
  traversal : RecInfoMinorTraversalShape
  traversal_eq : S.traversal = some traversal
  name : ctor.name = S.constructor.name
  fields : ctor.fields.length = traversal.fields.size
  recursivePositions : (InductiveSignature.Instance.recursiveFields (s := s) ctor).map Prod.fst =
    traversal.recursivePositions
  hypotheses : RecInfoMinorHypothesisTypeOrigins S.sourceFullContext S.recursiveFields S.hypotheses
  hypotheses_eq : S.hypothesis_type_origins = some hypotheses
  recursiveCount : (InductiveSignature.Instance.recursiveFields (s := s) ctor).length = S.hypotheses.size
  recursive : ∀ j (hj : j < (InductiveSignature.Instance.recursiveFields (s := s) ctor).length),
    ∃ root sourceType,
      ∃ O : RecInfoMinorHypothesisTypeOrigin hypotheses.stats hypotheses.recInfos
        root S.recursiveFields[j]! sourceType,
      ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
        BindingContextLE hypotheses.fieldRoot root ∧
        D.type = (sourceType.consumeTypeAnnotationsVerified
          S.sourceFullContext.env.isTypeAnnotationWrapper) ∧
        (InductiveSignature.Instance.recursiveFields (s := s) ctor)[j].2.target.val = O.ownerIdx ∧
        (InductiveSignature.Instance.recursiveFields (s := s) ctor)[j].2.binders.length = O.args.size

/-- One source-normalized generation witness, selected from the complete
actual construction before installation. The raw formation signature is not
forced to retain the consumed binder syntax of the generated declarations. -/
structure CompletedRecursorConstruction.ConsumedGeneration
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) where
  signature : InductiveSignature
  generation : InductiveSignature.Instance signature
  models : signature.Models sourceEnv decl
  params : signature.params = R.parameterScope.toCtx.reverse
  families : signature.families = H.consumedFamilies
  admissible : generation.Admissible R.headerVEnv
  uvars : generation.uvars = (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
  levels : generation.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  target : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    H.elimLevel = some generation.targetLevel
  familyCount : signature.families.size = indTypes.size
  familyName : ∀ owner (howner : owner < signature.families.size),
    signature.families[owner].name = indTypes[owner]!.name
  names : ∀ owner, generation.recursorName owner = signature.families[owner].name.str "rec"
  constructorCount : signature.constructors.size = decl.ownedConstructors.length
  constructorOrder : List.Forall₂
    (fun ctor pair => signature.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name)
    signature.constructors.toList decl.ownedConstructors
  minorTranslation : TrExprS R.context.venv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
    (H.localContext.lctx.mkForall stats.params <|
      H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
      H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) (.sort .zero))
    (VExpr.wrapForalls (generation.params ++ generation.motives ++ generation.minors) (.sort .zero))
  types : ∀ owner (howner : owner < signature.families.size),
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (generation.recursorType ⟨owner, howner⟩)
  recursiveTypesWF : generation.RecursiveTypesWF R.context.venv
  familyTypesWF : signature.FamilyTypesWF R.context.venv decl.uvars
  sourceOrigins : ∀ owner (howner : owner < H.recInfos.size)
    localIndex (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
    ∃ index : Fin signature.constructors.size,
      index.val = recursorMinorOffset indTypes owner + localIndex ∧
      signature.constructors[index].owner.val = owner ∧
      signature.fieldTypes signature.constructors[index] = H.sourceFields owner howner localIndex hlocal ∧
      signature.constructors[index].indices = H.sourceConstructorIndices owner howner localIndex hlocal ∧
      Nonempty (ConsumedConstructorOrigins signature (H.origins.minorShapes owner howner localIndex hlocal)
        signature.constructors[index])

/-- The consumed signature's constructors carry the retained source origins
of their minors. -/
theorem CompletedRecursorConstruction.consumedSignature_origins
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    Nonempty (ConsumedConstructorOrigins (H.consumedSignature HU)
      (H.origins.minorShapes owner howner localIndex hlocal)
      (H.consumedConstructorAt HU owner howner localIndex hlocal)) := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, hHas, traversal, htrav, _, hfieldsT, _, _, _, _, _, _, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  obtain ⟨origins, horig, _, _⟩ :=
    (H.origins.minorShapes owner howner localIndex hlocal).hypothesisTypeOrigins_exists
      stats H.recInfos hHas
  have hspec := H.consumedShapes_spec HU owner howner localIndex hlocal
  have hrec := H.consumedConstructorAt_recursiveFields HU owner howner localIndex hlocal
  refine ⟨{
    traversal := traversal
    traversal_eq := htrav
    name := rfl
    fields := ?_
    recursivePositions := ?_
    hypotheses := origins
    hypotheses_eq := horig
    recursiveCount := ?_
    recursive := ?_ }⟩
  · simp [CompletedRecursorConstruction.consumedConstructorAt, H.sourceFields_length, hfieldsT]
  · rw [hrec]; exact hspec.1 traversal htrav
  · rw [hrec]; exact hspec.2.1
  · intro j hj
    have hj' : j < (H.consumedShapes HU owner howner localIndex hlocal).length := by
      rw [hrec] at hj; exact hj
    obtain ⟨root, sourceType, O, D, hLE, hD, htarget, hbinders⟩ := hspec.2.2.2.1 origins horig j hj'
    refine ⟨root, sourceType, O, D, hLE, hD, ?_, ?_⟩
    · rw [← htarget]
      exact congrArg (fun x => x.2.target.val) (List.getElem_of_eq hrec hj)
    · rw [← hbinders]
      exact congrArg (fun x => x.2.binders.length) (List.getElem_of_eq hrec hj)

/-- The junction, under the universe support of the hypothesis arguments: the
explicit generation witness whose signature is `H.consumedSignature HU`. -/
noncomputable def CompletedRecursorConstruction.consumedGenerationOf
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (HU : H.ArgumentUniverses) :
    H.ConsumedGeneration := by
  have D := H.consumedSignatureData HU
  have hfamCount : (H.consumedSignature HU).families.size = indTypes.size := by
    simp [H.consumedFamilies_size, H.sourceFamilyCount]
  refine {
    signature := H.consumedSignature HU
    generation := H.consumedInstance (H.consumedSignature HU)
    models := D.models
    params := rfl
    families := rfl
    admissible := H.consumedInstance_admissible D.uvars D.params D.families D.size
      (fun owner howner localIndex hlocal => by
        obtain ⟨hk, _, h2, h3, h4⟩ := D.constructor owner howner localIndex hlocal
        exact ⟨hk, h2, h3, h4⟩)
    uvars := rfl
    levels := rfl
    target := H.consumedInstance_target _
    familyCount := hfamCount
    familyName := ?_
    names := fun _ => rfl
    constructorCount := D.size
    constructorOrder := ?_
    minorTranslation := H.consumedSignature_minorTranslation HU
    types := H.consumedSignature_types HU
    recursiveTypesWF := H.consumedSignature_recursiveTypesWF HU
    familyTypesWF := H.consumedFamilyTypesWF rfl rfl
    sourceOrigins := ?_ }
  · intro owner howner
    have howner' : owner < H.recInfos.size := by
      simpa [H.consumedFamilies_size] using howner
    have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
    have hdeclOwner : owner < decl.types.length := by
      rw [← H.cardinality.records]; exact howner'
    have hname := D.family_name ⟨owner, howner⟩ owner howner' rfl
    have hownerTr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
      owner (by simpa using hsourceOwner) hdeclOwner
    have hsourceBang : indTypes[owner]! = indTypes[owner] := by
      simp [hsourceOwner]
    rw [hsourceBang]
    refine hname.trans ?_
    simpa using hownerTr.header.name
  · apply List.forall₂_of_getElem (by simp)
    intro k hk hk'
    obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex k hk'
    have hk2 : recursorMinorOffset indTypes owner + localIndex <
        (H.consumedSignature HU).constructors.size := by
      simpa using hk
    simp only [Array.getElem_toList]
    exact D.constructorNames owner howner localIndex hlocal hk2
  · intro owner howner localIndex hlocal
    obtain ⟨hk, _, hown, hft, hidx⟩ := D.constructor owner howner localIndex hlocal
    refine ⟨⟨recursorMinorOffset indTypes owner + localIndex, hk⟩, rfl, hown, hft, hidx, ?_⟩
    simp only [Fin.getElem_fin]
    rw [H.consumedSignature_constructor HU owner howner localIndex hlocal hk]
    exact H.consumedSignature_origins HU owner howner localIndex hlocal

/-- The generation witness: the explicit construction `consumedGenerationOf`
(not a choice from `canonicalConsumedGeneration`), so that its signature is
definitionally `H.consumedSignature H.argumentUniverses` and the facts
retained by the construction (for instance
`consumedGeneration_shapeTranslations`) are available about it. -/
noncomputable def CompletedRecursorConstruction.consumedGeneration
    (H : CompletedRecursorConstruction R) : H.ConsumedGeneration :=
  H.consumedGenerationOf H.argumentUniverses

theorem CompletedRecursorConstruction.consumedGeneration_signature
    (H : CompletedRecursorConstruction R) :
    H.consumedGeneration.signature = H.consumedSignature H.argumentUniverses := rfl

noncomputable def CompletedRecursorConstruction.generationSignature
    (H : CompletedRecursorConstruction R) : InductiveSignature := H.consumedGeneration.signature

noncomputable def CompletedRecursorConstruction.generationInstance
    (H : CompletedRecursorConstruction R) : InductiveSignature.Instance H.generationSignature :=
  H.consumedGeneration.generation

noncomputable def CompletedRecursorConstruction.nativeTarget
    (H : CompletedRecursorConstruction R) (owner : Nat) : VConstVal :=
  if h : owner < H.generationSignature.families.size then
    H.generationInstance.recursor ⟨owner, h⟩
  else { name := .anonymous, uvars := 0, type := .sort .zero }

theorem CompletedRecursorConstruction.nativeTarget_eq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < indTypes.size) :
    H.nativeTarget owner = {
      name := Lean.mkRecName indTypes[owner]!.name
      uvars := (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      type := (H.nativeTarget owner).type } := by
  have hf : owner < H.generationSignature.families.size := by
    simpa [generationSignature, H.consumedGeneration.familyCount] using howner
  simp only [nativeTarget, dif_pos hf, InductiveSignature.Instance.recursor]
  have hn := H.consumedGeneration.names ⟨owner, hf⟩
  have hfName := H.consumedGeneration.familyName owner hf
  change H.generationInstance.recursorName ⟨owner, hf⟩ = _ at hn
  rw [hn]
  simp only [generationInstance, H.consumedGeneration.uvars]
  congr 1
  exact congrArg (fun name : Name => name.str "rec") hfName

theorem CompletedRecursorConstruction.canonicalTypeTranslations
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < indTypes.size) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (H.nativeTarget owner).type := by
  have hf : owner < H.generationSignature.families.size := by
    simpa [generationSignature, H.consumedGeneration.familyCount] using howner
  simp only [nativeTarget, dif_pos hf, InductiveSignature.Instance.recursor]
  exact H.consumedGeneration.types owner hf

end Lean4Lean.VerifyInductive
