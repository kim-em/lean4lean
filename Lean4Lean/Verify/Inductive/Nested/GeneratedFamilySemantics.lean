import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.Nested.FamilyRealization
import Lean4Lean.Verify.Inductive.Nested.FormationNativeHeaderEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive


/-- A validated auxiliary is an exact source realization of a generated
family head after its independently recovered parameter context is converted
to the canonical production parameter context. -/
theorem ClosedNestedAuxiliaryTranslation.toGeneratedFamilyHeadRealization
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    Nonempty (GeneratedFamilyHeadRealization venv lparams parameterDomains
      (e.abstractList selection.fvars)) := by
  rcases H.residualAtDefEqParameterDomains henv parameterDomains Hcontexts with
    ⟨family, familyType, Hfamily, HfamilyType⟩
  exact ⟨{
    family := family
    familyType := familyType
    familyTyping := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HfamilyType
    sourceTranslation := Hfamily }⟩

/-- The concrete source head retained for a generated family is the original
nested-family constant applied to exactly the arguments used by auxiliary
construction, closed over that construction's parameter selection.  Its
translation is retained exactly, rather than only up to typing. -/
theorem GeneratedFamilyWitness.cachedFamilyHeadRealization
    (H : GeneratedFamilyWitness sourceEnv result.params
      finalState.nestedAux family)
    (Hmap : NestedAuxMapModels result finalState)
    {resultSelection : LocalForallSelection result.lctx result.params}
    (hresultNodup : resultSelection.fvars.Nodup)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      resultSelection)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : ∀ Haux : ClosedNestedAuxiliaryTranslation venv lparams
      result resultSelection H.data.nested,
      VEnv.IsDefEqCtx venv lparams.length [] parameterDomains.reverse
        Haux.domains.reverse) :
    Nonempty (GeneratedFamilyHeadRealization venv lparams parameterDomains
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars)) := by
  rcases H.closedAuxiliaryTranslation Hmap Htranslations with ⟨Haux⟩
  have Hrealized := Haux.toGeneratedFamilyHeadRealization henv
    parameterDomains (Hcontexts Haux)
  simpa only [H.cachedClosureAlpha resultSelection hresultNodup] using Hrealized

end VerifyInductive
end Lean4Lean
