import Lean4Lean.Verify.Inductive.Header.SemanticAssembly
import Lean4Lean.Verify.Inductive.Header.SemanticCompletion
import Lean4Lean.Verify.Inductive.Recursor.Structure

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkConstructors.loopTypes

/-- Check every constructor against the installed header-only semantic
declaration while accumulating the raw abstract constructor targets produced
by those same executable checks.  No constructor-bearing declaration is an
input: it is deliberately assembled only after this traversal finishes. -/
theorem accumulatesSemanticTargets
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {indTypes : Array InductiveType} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {headerEnv : Environment}
    (Hheader : ContextWF { c with env := headerEnv })
    (hmlctx : Hheader.mlctx = Hc.mlctx)
    (htypesAdded : Hc.venv.addConstVals
      (Hsemantic.headerDecl isUnsafe).typeConstants = some Hheader.venv)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (Hsemantic.headerDecl isUnsafe) depth)
    (hheaderParams : Hmaterialized.headers.params = commonParams)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hheader.venv stats.indConsts)
    (Hfinish : CheckedSourceConstructorRows Hheader.venv
      c.lparams indTypes.toList → Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
      { c with env := headerEnv }).WF Q := by
  let HmaterializedMono :=
    Hmaterialized.mono (VEnv.addConstVals_le htypesAdded)
  have hscope : Hc.mlctx.vlctx = Hheader.mlctx.vlctx :=
    congrArg TypeChecker.MLCtx.vlctx hmlctx.symm
  let Hmaterialized' : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hheader.venv c.lparams Hheader.mlctx.vlctx stats
        (Hsemantic.headerDecl isUnsafe) depth :=
    HmaterializedMono.retargetScope hscope
  let Hsuffix := Hmaterialized'.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      Hmaterialized'
  have hheaderParams' : Hmaterialized'.headers.params = commonParams :=
    by
      calc
        Hmaterialized'.headers.params =
            HmaterializedMono.headers.params := by
          exact checkInductiveTypes.loopInd.MaterializedHeaderResult.retargetScope_headers_params
            HmaterializedMono hscope
        _ = Hmaterialized.headers.params :=
          checkInductiveTypes.loopInd.MaterializedHeaderResult.mono_headers_params
            Hmaterialized (VEnv.addConstVals_le htypesAdded)
        _ = commonParams := hheaderParams
  have hparamsCtx : VEnv.IsDefEqCtx Hheader.venv
      (Hsemantic.headerDecl isUnsafe).uvars []
      commonParams.reverse Hsuffix.parameterDecls.toCtx := by
    simpa [Hsuffix,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.parameterSuffix,
      hheaderParams', Hmaterialized'.uvars] using
      Hmaterialized'.paramsContext
  apply checkConstructors.loopTypes.accumulatesRawTargets
    (stats := stats) (isUnsafe := isUnsafe) (indTypes := indTypes)
    (targetIdx := 0) (Q := Q) Hheader
    (by
      simpa using
        (CheckedSourceConstructorRows.empty Hheader.venv c.lparams))
  · intro familyIdx hfamily ctorIdx hctor checkedType Hchecked R hR
    have htarget : familyIdx <
        (Hsemantic.headerDecl isUnsafe).types.length := by
      simpa using hfamily
    let target := (Hsemantic.headerDecl isUnsafe).types[familyIdx]
    have Htarget := Hsemantic.headerTranslationAt
      (isUnsafe := isUnsafe) familyIdx (by simpa using hfamily)
    have htargetUvars : target.uvars =
        (Hsemantic.headerDecl isUnsafe).uvars :=
      Htarget.uvars.trans Hstats.uvars
    have htargetLookup : Hheader.venv.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      exact List.mem_map.mpr
        ⟨target, List.getElem_mem htarget, rfl⟩
    have htargetWF : target.toVConstant.WF Hheader.venv :=
      Htarget.wf.mono (VEnv.addConstVals_le htypesAdded)
    have htargetShape : (Hsemantic.headerDecl isUnsafe).TypeShape
        Hheader.venv commonParams target := by
      have hshape := Hmaterialized'.headers.typeShapes target
        (List.getElem_mem htarget)
      simpa [hheaderParams'] using hshape
    have HcheckedSemantic := checkConstructors.loopCtor.refinesCtorShape
      (isUnsafe := isUnsafe)
      (fuel := { c with env := headerEnv }.fuel.inductiveFuel)
      Hheader Hsuffix Hstats hparamsCtx
      Hchecked.source Hchecked.typing htarget rfl htargetUvars
      htargetLookup htargetWF htargetShape hconsume hlit
      (fun h => by simpa [checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.headerDecl]
        using h)
      (Hmaterialized'.universeBound familyIdx htarget)
    exact HcheckedSemantic.mono fun _ _ => hR
  · exact Hfinish

/-- The completed constructor traversal determines the final constructor-
bearing declaration, its full source header translation, and its exact
installed header target list. -/
theorem assemblesSemanticHeadersExact
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {indTypes : Array InductiveType} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {headerEnv : Environment}
    (Hheader : ContextWF { c with env := headerEnv })
    (hmlctx : Hheader.mlctx = Hc.mlctx)
    (htypesAdded : Hc.venv.addConstVals
      (Hsemantic.headerDecl isUnsafe).typeConstants = some Hheader.venv)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (Hsemantic.headerDecl isUnsafe) depth)
    (hheaderParams : Hmaterialized.headers.params = commonParams)
    (hcommonParams : commonParams.length = nparams)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hheader.venv stats.indConsts) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
      { c with env := headerEnv }).WF fun _ =>
        Nonempty (AssembledSemanticHeadersOf Hc.venv
          Hheader.venv c.lparams nparams indTypes.toList
            isUnsafe commonParams commonLevel Hsemantic) := by
  apply accumulatesSemanticTargets
    (Q := fun _ => Nonempty (AssembledSemanticHeadersOf Hc.venv
      Hheader.venv c.lparams nparams indTypes.toList isUnsafe
        commonParams commonLevel Hsemantic))
    Hheader hmlctx htypesAdded Hmaterialized hheaderParams
    hconsume hlit
  intro Hrows
  exact AssembledSemanticHeaders.ofTargetsExact Hsemantic Hrows hcommonParams
    (by simpa using htypesAdded)

end checkConstructors.loopTypes
end VerifyInductive
end Lean4Lean
