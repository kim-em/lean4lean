import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.SourceUniverses
import Lean4Lean.Verify.Inductive.Recursor.LoopUniverses
namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Constructor fields are opened from literal source syntax, with only
annotation consumption. Their accepted domains therefore stay in the source
universe scope even though the surrounding recursor context has a fresh level. -/
theorem CompletedRecursorConstruction.minorFieldSourceUniverses
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (hsourceOwner : owner < indTypes.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hindex : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars).levelParamsIn
      c.lparams = true := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨HS⟩ := H.minorSemantics owner howner localIndex hlocal
  obtain ⟨traversal, htraversal, _, _, _, Htr⟩ :=
    H.minorSourceReplay owner howner hsourceOwner localIndex hlocal hindex
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at Htr
  have Hsupport := HS.semantic.traversal.decisions.levelParamsIn
    HS.semantic.rootWF.toBindingContextWF Htr.levelParamsIn
  have Hfields : FieldUniverseSupport c.lparams HS.semantic.traversal.terminalContext S.fields := by
    simpa [HS.semantic.traversal_fields] using Hsupport.2
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have Hfull := Hfields.mono HS.semantic.fieldsRecent.toBoundFVarArray Hext
  have Hbound := S.fields_bound.mono HS.semantic.extension.contextLE
  simpa using Hfull.mkForall Hbound (body := .sort .zero) rfl

end VerifyInductive
end Lean4Lean
