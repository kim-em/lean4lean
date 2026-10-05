import Lean4Lean.Verify.Inductive.CompletedRecursorConstruction
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.CanonicalParameterReplay
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMotiveGroup
import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorModel
import Lean4Lean.Verify.Inductive.ConsumedTranslation

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
        D.type = sourceType.consumeTypeAnnotationsVerified ∧
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
  sourceOrigins : ∀ owner (howner : owner < H.recInfos.size)
    localIndex (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
    ∃ index : Fin signature.constructors.size,
      index.val = recursorMinorOffset indTypes owner + localIndex ∧
      signature.constructors[index].owner.val = owner ∧
      signature.fieldTypes signature.constructors[index] = H.sourceFields owner howner localIndex hlocal ∧
      signature.constructors[index].indices = H.sourceConstructorIndices owner howner localIndex hlocal ∧
      Nonempty (ConsumedConstructorOrigins signature (H.origins.minorShapes owner howner localIndex hlocal)
        signature.constructors[index])

/-- The common parameter translation follows from its retained source choice;
it is already proved before the remaining motive/minor construction. -/
theorem CompletedRecursorConstruction.ConsumedGeneration.parameterTranslation
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorConstruction R} (G : H.ConsumedGeneration) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params (.sort .zero))
      (VExpr.wrapForalls G.generation.params (.sort .zero)) := by
  simpa only [InductiveSignature.Instance.params, G.params, G.levels] using
    H.sourceParameterTranslation

/-- The fixed family table and parameter choice determine every motive
binder. This translation is reconstructed from the actual first-pass origins. -/
theorem CompletedRecursorConstruction.ConsumedGeneration.motiveTranslation
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorConstruction R} (G : H.ConsumedGeneration) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params <|
        H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero))
      (VExpr.wrapForalls (G.generation.params ++ G.generation.motives) (.sort .zero)) :=
  H.generatedParametersMotivesTranslation G.generation G.params G.families G.levels G.target

/-- Construct the joint witness from actual parameter, motive, constructor,
and loopU traces. Annotation consumption uses the retained source expression
at each binder; recursive WHNF domain choices are made here, once, rather
than recovered from an independently chosen raw formation normal form. -/
theorem CompletedRecursorConstruction.canonicalConsumedGeneration
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) : Nonempty H.ConsumedGeneration := by
  sorry

noncomputable def CompletedRecursorConstruction.consumedGeneration
    (H : CompletedRecursorConstruction R) : H.ConsumedGeneration :=
  Classical.choice H.canonicalConsumedGeneration

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
