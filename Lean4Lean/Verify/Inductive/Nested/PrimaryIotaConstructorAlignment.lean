import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaOperationalAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Constructor semantics retained with operational restoration identity -/

/-- Lockstep constructor evidence which retains both the lowering mapping and
the source-facing abstract constructor semantics at that exact restoration
step.  This is the earliest safe place to establish the constructor half of
restored primary-iota LHS typing. -/
inductive RestoredConstructorSemanticMappingTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name)
    (canonicalEnv : VEnv) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → List VConstVal → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      RestoredConstructorSemanticMappingTrace result mappingEnv loweredEnv
        params nparams safety lparams canonicalEnv [] state [] state
          sourceProdEnv sourceProdEnv []
  | cons
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hsemantic : RestoredSourceConstructorSemantics lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredConstructorSemanticMappingTrace result mappingEnv
        loweredEnv params nparams safety lparams canonicalEnv sources
          nextState targets finalState middleProdEnv targetProdEnv
            constructors) :
      RestoredConstructorSemanticMappingTrace result mappingEnv loweredEnv
        params nparams safety lparams canonicalEnv (source :: sources) state
          (target :: targets) finalState sourceProdEnv targetProdEnv
            (Hsemantic.constructor :: constructors)

/-- Re-run the source-constructor interpretation while retaining the exact
operational mapping step instead of immediately projecting it away. -/
theorem RestoredConstructorMappingTrace.sourceSemanticMapping
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    RestoredConstructorSemanticMappingTrace result mappingEnv loweredEnv
      params nparams safety lparams canonicalEnv sources state targets
        finalState sourceProdEnv targetProdEnv constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _ _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i constructor constructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type constructor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type constructor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) constructor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredConstructorSemanticMappingTrace.cons Hmapping Hstep
          hsafety hlevels hname htype
          { constructor := constructor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

/-- Pointwise selection preserves the shared operational step and abstract
constructor identity. -/
theorem RestoredConstructorSemanticMappingTrace.at
    (H : RestoredConstructorSemanticMappingTrace result mappingEnv loweredEnv
      params nparams safety lparams canonicalEnv sources state targets
        finalState sourceProdEnv targetProdEnv constructors)
    (i : Nat) (hsource : i < sources.length)
    (htarget : i < targets.length) (hconstructor : i < constructors.length) :
    ∃ before after stepSource stepTarget,
      ∃ Hmapping : LoweredConstructorMapping mappingEnv params nparams result
          sources[i] before (targets[i], after),
      ∃ Hstep : RestoredConstructorStep result loweredEnv targets[i].name
          stepSource stepTarget,
      ∃ Hsemantic : RestoredSourceConstructorSemantics lparams safety
          canonicalEnv Hstep sources[i],
        Hstep.oldInfo.name = targets[i].name ∧
        Hsemantic.constructor = constructors[i] := by
  induction H generalizing i with
  | nil => simp at hsource
  | cons Hmapping Hstep hsafety hlevels hname htype Hsemantic Hrest ih =>
    cases i with
    | zero => exact ⟨_, _, _, _, Hmapping, Hstep, Hsemantic, hname, rfl⟩
    | succ i =>
      simpa using ih i (by simpa using hsource) (by simpa using htarget)
          (by simpa using hconstructor)

end VerifyInductive
end Lean4Lean
