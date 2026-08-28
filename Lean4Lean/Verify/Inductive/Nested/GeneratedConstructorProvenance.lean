import Lean4Lean.Verify.Inductive.Nested.LoweringTrace

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A constructor of a dynamically generated source family comes from the
constructor at the same position in the nested family from which the
auxiliary was built.  This is the constructor-level inverse needed after a
`FinalLoweredFamilyOrigin.generated` classification. -/
theorem GeneratedFamilyWitness.constructorAt
    (H : GeneratedFamilyWitness env params nestedAux family)
    (i : Nat) (hi : i < family.ctors.length) :
    ∃ hsource : i < H.sourceInfo.ctors.length,
      BuiltAuxConstructor env H.lctx H.As H.levels H.nestedNParams H.args
        H.sourceName H.auxName H.sourceInfo.ctors[i] H.data.type.ctors[i]! := by
  have htarget : i < H.data.type.ctors.length := by
    simpa [H.family_eq] using hi
  have hsource : i < H.sourceInfo.ctors.length := by
    rw [H.built.constructors_length]
    exact htarget
  rcases H.built.constructorAt i hsource with ⟨htarget', Hconstructor⟩
  refine ⟨hsource, ?_⟩
  simpa [getElem!_pos H.data.type.ctors i htarget'] using Hconstructor

/-- Positional provenance for a constructor of a generated family after
lowering.  The package connects the original nested-family constructor to the
generated constructor built from it and then to the final lowered
constructor.  All three selections retain their array/list lookup equations;
no constructor-name injectivity is required. -/
theorem GeneratedFamilyWitness.loweredConstructorAt
    (Hgenerated : GeneratedFamilyWitness env params nestedAux family)
    (Hmapping : LoweredInductiveMapping env params nparams finalResult family
      state out)
    (i : Nat) (hi : i < out.1.ctors.length) :
    ∃ sourceCtor generatedCtor finalCtor before after,
        i < Hgenerated.sourceInfo.ctors.length ∧
        Hgenerated.sourceInfo.ctors[i]? = some sourceCtor ∧
        family.ctors[i]? = some generatedCtor ∧
        out.1.ctors[i]? = some finalCtor ∧
        BuiltAuxConstructor env Hgenerated.lctx Hgenerated.As
          Hgenerated.levels Hgenerated.nestedNParams Hgenerated.args
          Hgenerated.sourceName Hgenerated.auxName sourceCtor generatedCtor ∧
        LoweredConstructorMapping env params nparams finalResult generatedCtor
          before (finalCtor, after) := by
  have hfamily : i < family.ctors.length := by
    rw [← Hmapping.constructors.length]
    exact hi
  rcases Hgenerated.constructorAt i hfamily with ⟨hsource, Hbuilt⟩
  rcases Hmapping.constructors.mappingAt i hfamily with
    ⟨generatedCtor, finalCtor, before, after, hgenerated, hfinal, Hctor⟩
  have hdataBound : i < Hgenerated.data.type.ctors.length := by
    simpa [← Hgenerated.family_eq] using hfamily
  have hdataGet : Hgenerated.data.type.ctors[i]? = some generatedCtor := by
    simpa [Hgenerated.family_eq] using hgenerated
  have hdataElem : Hgenerated.data.type.ctors[i] = generatedCtor := by
    simpa [hdataBound] using hdataGet
  have hdataBang : Hgenerated.data.type.ctors[i]! = generatedCtor := by
    simpa [getElem!_pos Hgenerated.data.type.ctors i hdataBound] using hdataElem
  let sourceCtor := Hgenerated.sourceInfo.ctors[i]
  refine ⟨sourceCtor, generatedCtor, finalCtor, before, after, hsource,
    ?_, hgenerated, hfinal, ?_, Hctor⟩
  · simp [sourceCtor, hsource]
  · simpa [sourceCtor, hdataBang] using Hbuilt

end VerifyInductive
end Lean4Lean
