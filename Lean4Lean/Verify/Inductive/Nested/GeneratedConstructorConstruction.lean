import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilyConstruction
import Lean4Lean.Verify.Inductive.Nested.GeneratedConstructorProvenance
import Lean4Lean.Verify.Inductive.Nested.GeneratedQueueOrigins

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Exact construction provenance for generated constructors -/

/-- One final constructor of a generated queue family, connected at the same
array position to all three producer-owned stages:

* the source constructor selected by `BuiltAuxiliary`;
* the concrete generated constructor before recursive lowering; and
* the final constructor after the queue's lowering step.

`translation` additionally connects that exact source position to the
constructor of the finitely installed abstract container. -/
structure FinalLoweredGeneratedFamilyOrigin.BuiltConstructorTranslation
    {ves : VEnvs}
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      target)
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
      params finalState.nestedAux H.source H.generated)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (Hmap : NestedAuxMapModels result finalState)
    (i : Nat) (hi : i < target.ctors.length) where
  sourceCtor : Name
  generatedCtor : Constructor
  finalCtor : Constructor
  before : Lean4Lean.ElimNestedInductive.State
  after : Lean4Lean.ElimNestedInductive.State
  sourceIdx_lt : i < H.generated.sourceInfo.ctors.length
  sourceLookup : H.generated.sourceInfo.ctors[i]? = some sourceCtor
  generatedLookup : H.source.ctors[i]? = some generatedCtor
  finalLookup : target.ctors[i]? = some finalCtor
  built : BuiltAuxConstructor prodEnv H.generated.lctx H.generated.As
    H.generated.levels H.generated.nestedNParams H.generated.args
    H.generated.sourceName H.generated.auxName sourceCtor generatedCtor
  lowering : LoweredConstructorMapping prodEnv params nparams result
    generatedCtor before (finalCtor, after)
  translation : C.BuiltConstructorTranslation i sourceIdx_lt

/-- The actual final queue mapping and persistent environment alignment
construct the complete positional package above.  In particular, no source
constructor translation or residual is supplied by a caller. -/
theorem FinalLoweredGeneratedFamilyOrigin.builtConstructorTranslation
    {ves : VEnvs}
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      target)
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
      params finalState.nestedAux H.source H.generated)
    (wf : ves.WF prodEnv)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (Hmap : NestedAuxMapModels result finalState)
    (i : Nat) (hi : i < target.ctors.length) :
    Nonempty (H.BuiltConstructorTranslation C result Hmap i hi) := by
  have Hmapping := H.finalMapping Hmap
  rcases H.generated.loweredConstructorAt Hmapping i hi with
    ⟨sourceCtor, generatedCtor, finalCtor, before, after, hsource,
      hsourceLookup, hgeneratedLookup, hfinalLookup, Hbuilt, Hlowering⟩
  rcases C.builtConstructorTranslation wf i hsource with ⟨Htranslation⟩
  exact ⟨{
    sourceCtor := sourceCtor
    generatedCtor := generatedCtor
    finalCtor := finalCtor
    before := before
    after := after
    sourceIdx_lt := hsource
    sourceLookup := hsourceLookup
    generatedLookup := hgeneratedLookup
    finalLookup := hfinalLookup
    built := Hbuilt
    lowering := Hlowering
    translation := Htranslation }⟩

end VerifyInductive
end Lean4Lean
