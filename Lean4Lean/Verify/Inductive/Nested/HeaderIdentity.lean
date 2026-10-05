import Lean4Lean.Verify.Inductive.Nested.FormationExpansionTrace
import Lean4Lean.Verify.Typing.TranslationIdentity

namespace Lean4Lean
namespace VerifyInductive

/-- Lowering keeps each original family header literally. Primitive abstract
projection syntax lets both translations retain that identity as well. -/
theorem LoweredInductiveMapping.headerIdentity
    (mapping : LoweredInductiveMapping prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (left : TrInductiveTypeHeaders env envTypes lparams sourceConcrete source)
    (right : TrInductiveType env targetEnvTypes lparams targetConcrete target) :
    source.toVConstVal = target.toVConstVal := by
  have hname := left.header.name.trans (mapping.name.symm.trans right.header.name.symm)
  have huvars := left.header.uvars.trans right.header.uvars.symm
  have htype := left.header.type.identity (mapping.type ▸ right.header.type)
  rcases source with ⟨⟨⟨su, st⟩, sn⟩, si, sl, sc⟩
  rcases target with ⟨⟨⟨tu, tt⟩, tn⟩, ti, tl, tc⟩
  simp_all

/-- Actual positional lowering provenance fixes the entire original header
prefix, without a semantic comparison of two abstract header translations. -/
theorem NestedLoweringResultClosed.originalHeaderIdentity
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (lowering : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (left : TrInductDeclCore env lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (right : TrInductDeclCore env lparams nparams result.types
      isUnsafe expandedDecl targetEnvTypes targetEnvCtors)
    (empty : initialState.nestedAux = #[])
    (position : Nat) (bound : position < sourceDecl.types.length) :
    ∃ targetBound : position < expandedDecl.types.length,
      sourceDecl.types[position].toVConstVal =
        expandedDecl.types[position].toVConstVal := by
  have sourceLength := TrInductDeclCore.types_length left
  have targetLength := TrInductDeclCore.types_length right
  have sourceBound : position < sourceTypes.length := by omega
  have resultBound : position < result.types.length :=
    Nat.lt_of_lt_of_le sourceBound lowering.toResult.sourceTypes_length_le
  have targetBound : position < expandedDecl.types.length := by omega
  obtain ⟨_, _, concrete, _, _, _, _, mapping, selected⟩ :=
    lowering.sourceFinalMappingAtFreshAligned empty sourceBound
  obtain ⟨_, selectedEq⟩ := _root_.getElem?_eq_some_iff.mp selected
  have target := TrInductDeclCore.typeAt right position resultBound targetBound
  rw [selectedEq] at target
  exact ⟨targetBound, mapping.headerIdentity
    (TrInductiveType.headers (TrInductDeclCore.typeAt left position sourceBound bound)) target⟩

/-- The actual original header list is the literal expanded prefix. -/
theorem NestedLoweringResultClosed.typeConstantsPrefix
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (lowering : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (left : TrInductDeclCore env lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (right : TrInductDeclCore env lparams nparams result.types
      isUnsafe expandedDecl targetEnvTypes targetEnvCtors)
    (empty : initialState.nestedAux = #[]) :
    sourceDecl.typeConstants = expandedDecl.typeConstants.take sourceDecl.types.length := by
  have sourceLength := TrInductDeclCore.types_length left
  have targetLength := TrInductDeclCore.types_length right
  have prefixLength := lowering.toResult.sourceTypes_length_le
  have bound : sourceDecl.types.length ≤ expandedDecl.types.length := by omega
  apply List.ext_getElem
  · simp [VInductDecl.typeConstants, Nat.min_eq_left bound]
  · intro position leftBound rightBound
    have sourceBound : position < sourceDecl.types.length := by
      simpa [VInductDecl.typeConstants] using leftBound
    obtain ⟨_, same⟩ := lowering.originalHeaderIdentity left right empty position sourceBound
    simpa [VInductDecl.typeConstants] using same

/-- If lowering added no families, its independently translated abstract
header environments are identical. Constructor translations are immaterial. -/
theorem NestedLoweringResultClosed.typeConstantsIdentity
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (lowering : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (left : TrInductDeclCore env lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (right : TrInductDeclCore env lparams nparams result.types
      isUnsafe expandedDecl targetEnvTypes targetEnvCtors)
    (empty : initialState.nestedAux = #[])
    (lengths : expandedDecl.types.length = sourceDecl.types.length) :
    sourceDecl.typeConstants = expandedDecl.typeConstants := by
  apply List.ext_getElem
  · simpa [VInductDecl.typeConstants] using lengths.symm
  · intro position leftBound rightBound
    have bound : position < sourceDecl.types.length := by
      simpa [VInductDecl.typeConstants] using leftBound
    obtain ⟨_, same⟩ := lowering.originalHeaderIdentity left right empty position bound
    simpa [VInductDecl.typeConstants] using same

end VerifyInductive
end Lean4Lean
