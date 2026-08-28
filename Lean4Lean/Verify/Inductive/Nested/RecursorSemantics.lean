import Lean4Lean.Verify.Inductive.Equation.Setup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- A flattened minor's row witness also determines the bound needed to
select its retained source shape.  The row stores its bound against the
operational `RecInfo.minors` array; the origin table has the same size by
construction. -/
theorem RecInfoTypeOrigins.FlatMinorOrigin.shapeBound
    {c : AddInductive.Context} {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoTypeOrigins c recInfos} {minorIdx : Nat}
    {D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) minorIdx}
    (O : H.FlatMinorOrigin D) :
    O.localIndex < H.minorTypes[O.owner]!.size := by
  rw [(H.minors O.owner O.owner_lt).size_eq]
  simpa [getElem!_pos recInfos O.owner O.owner_lt] using O.local_lt

/-- The canonical retained source shape selected by a flattened minor
origin.  Naming this projection keeps subsequent semantic statements stable
under proof irrelevance of the row-size bound. -/
def RecInfoTypeOrigins.FlatMinorOrigin.shape
    {c : AddInductive.Context} {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoTypeOrigins c recInfos} {minorIdx : Nat}
    {D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) minorIdx}
    (O : H.FlatMinorOrigin D) : RecInfoMinorTypeShape :=
  H.minorShapes O.owner O.owner_lt O.localIndex O.shapeBound

/-- Complete source-facing package for one declaration selected from the
flattened minor array.  It combines the row inverse with the independent
constructor/traversal alignment and the semantic first-pass witness.  In
particular, callers no longer need to reconstruct a potentially different
`RecInfoMinorTypeShape` by replaying the `flatMap` bookkeeping. -/
structure RecursorPhasesResult.FlatMinorSemanticSource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    {minorIdx : Nat}
    (D : BoundFVarDeclarationAt H.localContext
      (H.recInfos.flatMap (·.minors)) minorIdx)
    (O : H.origins.FlatMinorOrigin D) : Prop where
  sourceOwner_lt : O.owner < indTypes.size
  origin_minorType : O.shape.origin =
    H.origins.minorTypes[O.owner]![O.localIndex]!
  origin_eq : O.shape.origin = D.type
  localIndex_eq : O.shape.localIndex = O.localIndex
  sourceConstructors_eq :
    O.shape.sourceConstructors = indTypes[O.owner]!.ctors
  hypothesisTypeOrigins :
    O.shape.HasHypothesisTypeOrigins stats H.recInfos
  traversal : ∃ traversal,
    O.shape.traversal = some traversal ∧
    traversal.constructor = O.shape.constructor ∧
    traversal.fields = O.shape.fields ∧
    traversal.recursiveFields = O.shape.recursiveFields ∧
    traversal.stats = stats ∧
    AddInductive.isValidIndApp? stats traversal.terminal = some
      (AddInductive.getIIndices stats traversal.terminal).1 ∧
    O.shape.motiveApp = (
      let (motiveOwner, indices) :=
        AddInductive.getIIndices stats traversal.terminal
      Expr.app
        (mkAppN H.recInfos[motiveOwner]!.motive indices)
        (mkAppN
          (mkAppN (.const O.shape.constructor.name stats.levels)
            stats.params)
          O.shape.fields)) ∧
    BindingContextLE traversal.rootContext H.localContext ∧
    BindingContextLE traversal.terminalContext H.localContext ∧
    BindingContextLE O.shape.sourceFullContext H.localContext
  semantic : Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF O.shape
    H.parameterSuffix.parameterDecls)

/-- The source-shape package identifies the exact constructor selected by
the flattened row, not only its containing constructor list. -/
theorem RecursorPhasesResult.FlatMinorSemanticSource.constructorAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {minorIdx : Nat}
    {D : BoundFVarDeclarationAt H.localContext
      (H.recInfos.flatMap (·.minors)) minorIdx}
    {O : H.origins.FlatMinorOrigin D}
    (P : RecursorPhasesResult.FlatMinorSemanticSource H D O) :
    indTypes[O.owner]!.ctors[O.localIndex]? = some O.shape.constructor := by
  have hconstructor := O.shape.sourceConstructor
  rw [P.sourceConstructors_eq, P.localIndex_eq] at hconstructor
  exact hconstructor

/-- Retrieve the canonical source shape and its semantic witness from the
completed recursor phases.  This is the stable end-to-end entry point for a
minor-domain proof: all facts come from `minorSources` and `minorSemantics`,
while the flattened declaration is related back to the same origin by the
supplied `FlatMinorOrigin`. -/
theorem RecursorPhasesResult.minorSemanticSourceOfFlatOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (D : BoundFVarDeclarationAt H.localContext
      (H.recInfos.flatMap (·.minors)) minorIdx)
    (O : H.origins.FlatMinorOrigin D)
    (hsourceOwner : O.owner < indTypes.size) :
    RecursorPhasesResult.FlatMinorSemanticSource H D O := by
  let S := O.shape
  have Hsource := H.minorSources O.owner O.owner_lt hsourceOwner O.localIndex
    O.shapeBound
  have Hsemantic := H.minorSemantics O.owner O.owner_lt O.localIndex
    O.shapeBound
  change S.origin =
        H.origins.minorTypes[O.owner]![O.localIndex]! ∧
      S.localIndex = O.localIndex ∧
      S.sourceConstructors = indTypes[O.owner]!.ctors ∧
      S.HasHypothesisTypeOrigins stats H.recInfos ∧
      (∃ traversal, S.traversal = some traversal ∧
        traversal.constructor = S.constructor ∧
        traversal.fields = S.fields ∧
        traversal.recursiveFields = S.recursiveFields ∧
        traversal.stats = stats ∧
        AddInductive.isValidIndApp? stats traversal.terminal = some
          (AddInductive.getIIndices stats traversal.terminal).1 ∧
        S.motiveApp = (
          let (motiveOwner, indices) :=
            AddInductive.getIIndices stats traversal.terminal
          Expr.app
            (mkAppN H.recInfos[motiveOwner]!.motive indices)
            (mkAppN
              (mkAppN (.const S.constructor.name stats.levels) stats.params)
              S.fields)) ∧
        BindingContextLE traversal.rootContext H.localContext ∧
        BindingContextLE traversal.terminalContext H.localContext ∧
        BindingContextLE S.sourceFullContext H.localContext) at Hsource
  rcases Hsource with
    ⟨horigin, hlocal, hconstructors, hhypotheses, Htraversal⟩
  refine {
    sourceOwner_lt := hsourceOwner
    origin_minorType := ?_
    origin_eq := ?_
    localIndex_eq := ?_
    sourceConstructors_eq := ?_
    hypothesisTypeOrigins := ?_
    traversal := ?_
    semantic := ?_ }
  · simpa [S] using horigin
  · simpa [S] using horigin.trans O.originType_eq.symm
  · simpa [S] using hlocal
  · simpa [S] using hconstructors
  · simpa [S] using hhypotheses
  · simpa [S] using Htraversal
  · simpa [S, RecInfoTypeOrigins.FlatMinorOrigin.shape] using Hsemantic

end VerifyInductive
end Lean4Lean
