import Lean4Lean.Verify.Inductive.Nested.Restoration.Run
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExpansionInverse
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources

/-! Universe arguments of the auxiliary occurrences in the lowered constructor
types of a validated nested run.

The executable lowering emits every auxiliary occurrence at `state.lvls`,
which is initialised to the declaration's level parameters and never modified.
The lowering relations record this through `NestedAuxLE` (which fixes `lvls`),
the `lvls` fields of `ConstructorLowering`,
`ConstructorLowering.Resolved` and `NestedLowering`, and the universe-argument
premise of the replacement leaves in
`NestedLoweringOutputClosed.sourceExpansionsAboveLvls`. Projected through
the translation, every replaced occurrence is a level leaf
(`NodeReplacementResolved.levelLeaf`), so the lowered constructor types of
the source families use the auxiliary family and constructor names only at
`VLevel.params sourceDecl.uvars` (`NestedRun.loweredConstructorLevels`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- **Every replaced occurrence at the declaration's universe parameters is a
level leaf.** A replacement emitted while the lowering state carries the universe
arguments `lparams.map .param` translates to an auxiliary head at
`VLevel.params`; its common-parameter arguments are bound variables, and its
trailing arguments copy the source's up to an expansion whose leaves are level
leaves again. -/
theorem NodeReplacementResolved.levelLeaf
    {names : List Name} {sourceDecl : VInductDecl} {lparams : List Name}
    {result : Lean4Lean.ElimNestedInductive.Result}
    (hlparams : lparams.Nodup) (huvars : sourceDecl.uvars = lparams.length)
    (hparamsSize : result.params.size = sourceDecl.nparams)
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)))
    {lctx : LocalContext} {As : Array Expr}
    {input state output nextState traceFinalState depth fieldDepth sourceValue
      targetValue sourceCtx targetCtx}
    (Htrace : NodeReplacementResolved prodEnv lctx result.params As input state
      output nextState result traceFinalState)
    (Hctx : NestedExpansionLookupCtx
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)) depth sourceCtx targetCtx)
    (selection : CDeclArray lctx As)
    (Harity : As.size = result.params.size)
    (Hdepth : depth = selection.fvars.length + fieldDepth)
    (HtargetParams : SelectedParameterTargets selection.fvars fieldDepth targetCtx)
    (HsourceExpr : TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue)
    (HtargetExpr : TrExprS targetTypesVEnv lparams targetCtx output targetValue)
    (hlvls : state.lvls = lparams.map Level.param) :
    VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars) depth sourceValue
      targetValue := by
  have hselectionLength : selection.fvars.length = sourceDecl.nparams := by
    calc
      selection.fvars.length = As.size := selection.size.symm
      _ = result.params.size := Harity
      _ = sourceDecl.nparams := hparamsSize
  have HbaseDepth : sourceDecl.nparams ≤ depth := by
    rw [Hdepth, ← hselectionLength]
    omega
  rcases Htrace.targetSpine selection Harity HtargetParams hparamsSize HtargetExpr with ⟨T⟩
  rcases T.sourceSpine HsourceExpr with ⟨S⟩
  have Htrailing := TrExprS.forall₂_abstractExpansionAbove Hlift Hctx HbaseDepth
    S.trailingTranslation T.trailingTranslation
  have hauxLevels : T.auxiliaryLevels = VLevel.params sourceDecl.uvars := by
    have h := T.auxiliaryLevelsTranslation
    rw [T.concreteAuxLevels_eq, hlvls,
      checkInductiveTypes.loopInd.VLevel.mapM_ofLevel_paramNames,
      Lean4Lean.VerifyInductive.List.map_param_idxOf_eq_params hlparams] at h
    rw [huvars]
    exact (Option.some.inj h).symm
  intro hs
  rw [S.sourceValue_eq, VExpr.containsAnyConst_mkApps_eq_false_iff] at hs
  rw [T.targetValue_eq, VExpr.constLevelsAt_mkApps]
  refine ⟨fun _ => hauxLevels, ?_⟩
  intro arg harg
  rcases List.mem_append.mp harg with hparam | htrailing
  · simp only [VInductDecl.paramVars, List.mem_map] at hparam
    obtain ⟨_, _, rfl⟩ := hparam
    trivial
  · obtain ⟨source, hsource, Hexp⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Htrailing arg htrailing
    exact Hexp.constLevelsAt (fun h => h)
      (hs.2 source (List.mem_append_right _ hsource))

/-- `LoweredAuxiliaryFamily.abstractExpansion` for an arbitrary
liftable leaf relation, with every replacement known to be emitted at the
universe arguments of the final lowering state. -/
theorem LoweredAuxiliaryFamily.abstractExpansionAboveLvls
    {prodEnv : Environment} {params : Array Expr} {nparams : Nat}
    {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType} {baseVEnv sourceTypesVEnv targetTypesVEnv : VEnv}
    {lparams : List Name} {target : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {decl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove decl.nparams leaf)
    (H : LoweredAuxiliaryFamily prodEnv params nparams finalState
      targetConcrete)
    (Hsource : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (Htarget : TrInductiveType baseVEnv targetTypesVEnv lparams targetConcrete
      target)
    (Hmap : NestedAuxMapModels result finalState)
    (henv : baseVEnv.WF)
    (huvars : decl.uvars = lparams.length)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (HtargetTypesWF : targetTypesVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState' depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState' →
      NestedExpansionLookupCtx leaf depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue →
      TrExprS targetTypesVEnv lparams targetCtx output targetValue →
      state.lvls = finalState.lvls →
      leaf depth sourceValue targetValue) :
    VInductDecl.NestedTypeExpansion baseVEnv decl leaf Hsource.source target := by
  have Hmapping := H.resolvedMapping Hmap
  have Hheader : NestedTypeExpansionHeader baseVEnv decl Hsource.source target :=
    Hmapping.abstractHeaderExpansion Hsource.translation Htarget henv huvars
      Hsource.numIndices Hsource.resultLevel
  have hstep : H.stepState.lvls = finalState.lvls :=
    H.lowered.nestedAuxLE.lvls.symm.trans H.later.lvls.symm
  exact Hmapping.abstractExpansionAbove Hlift hstep Hsource.translation Htarget Hheader
    (Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.constructorsClosed
      Hsource.translation)
    HsourceTypesWF HtargetTypesWF hparamsSize hnparams Hhit

end VerifyInductive
end Lean4Lean
