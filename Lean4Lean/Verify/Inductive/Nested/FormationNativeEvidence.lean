import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilySemantics
import Lean4Lean.Verify.Inductive.Nested.FormationExpansionTrace
import Lean4Lean.Verify.Inductive.Nested.FormationNativeHeaderEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Producer-owned nested formation evidence

This module joins the concrete auxiliary builder to the independently
validated, closed source-family translation retained by restoration.  The
results are indexed by the exact generated-family witness; they do not expose
a caller-supplied replacement or generated-family compatibility boundary.
-/

/-- Formation uses the declaration's original universe parameters.  At that
universe observer, the first source header and the native auxiliary
validation derive exactly the same common-parameter context.  This is the
small-elimination specialization of the recursor-facing context theorem, but
it is proved directly so formation does not depend on a completed recursor
phase. -/
theorem NestedLoweringResultClosed.auxiliaryFormationParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (hempty : initialState.nestedAux = #[])
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation envCtors c.lparams
      result selection e) :
    let Hsuffix := Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
      (elimLevel := .zero) (by trivial)
    let parameterDomains := Hsuffix.parameterDecls.toCtx.reverse
    VEnv.IsDefEqCtx envCtors c.lparams.length []
      parameterDomains.reverse Haux.domains.reverse := by
  dsimp only [AddInductive.getRecLevelParams]
  have HsourceClosed : ∀ source ∈ sourceTypes,
      source.type.FVarsIn fun _ => False := by
    intro source hsource
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hsource.types source
        hsource with ⟨target, _htarget, Htarget⟩
    exact Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  rcases H.sourceParameterPrefix HsourceClosed e with
    ⟨first, rest, residual, hsourceTypes, Htelescope, Hsame⟩
  subst sourceTypes
  have hfamily : 0 < (first :: rest).length := by simp
  rcases H.sourceHeaderTranslationAtFresh hempty R.core 0 hfamily with
    ⟨hdecl, Hheader⟩
  have Hheader' : TrSourceConst Hheaders.sourceContext.venv c.lparams
      first.name first.type (loweredDecl.types[0]'hdecl).toVConstVal := by
    rw [Hheaders.sourceContextVEnv]
    simpa using Hheader
  have Htelescope' : Expr.ForallTelescope first.type loweredDecl.nparams
      residual := by
    rw [R.core.nparams]
    exact Htelescope
  rcases Hheaders.sourceMaterialized.sourceParameterDomainsAt first
      loweredDecl.types[0] Hheader' (List.getElem_mem hdecl)
      (elimLevel := .zero) (by trivial) Htelescope' with
    ⟨sourceDomains, sourceResidual, hsourceDomains,
      HsourceTranslation, HsourceContext⟩
  simp only [AddInductive.getRecLevelParams] at HsourceTranslation
    HsourceContext
  rw [Hheaders.sourceContextVEnv] at HsourceTranslation HsourceContext
  have hsourceLE : sourceVEnv ≤ envCtors :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      (VEnv.addConstVals_le Hsource.ctorsAdded)
  have hsourceWF : sourceVEnv.WF := by
    have hwf := Hheaders.sourceContext.checking.tr.wf
    rw [Hheaders.sourceContextVEnv] at hwf
    exact hwf
  have henv : envCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have HsourceTranslation' : TrExprS envCtors c.lparams [] first.type
      (VExpr.wrapForalls sourceDomains sourceResidual) :=
    HsourceTranslation.mono hsourceLE
  have HauxClosed : TrExprS envCtors c.lparams []
      (result.lctx.mkForall result.params e)
      (VExpr.wrapForalls Haux.domains Haux.residualTarget) := by
    rw [← Haux.target]
    exact Haux.closed
  have HauxSource : VEnv.IsDefEqCtx envCtors c.lparams.length []
      Haux.domains.reverse sourceDomains.reverse := by
    have hauxDomains : Haux.domains.length = nparams :=
      Haux.arity.trans (H.resultParamsSize.trans H.toResult.resultNParams)
    have Hcontexts := Hsame.translatedContextsExact henv
      (.refl henv (by trivial)) HauxClosed HsourceTranslation'
      hauxDomains (by simpa [R.core.nparams] using hsourceDomains)
    simpa [VLCtx.toCtx] using Hcontexts
  have HsourceContext' := HsourceContext.mono hsourceLE
  have HparameterSource := HsourceContext'.symm henv.ordered
  have HsourceAux := HauxSource.symm henv.ordered
  have HparameterAux := VEnv.IsDefEqCtx.transEmpty henv
    HparameterSource HsourceAux
  simpa using HparameterAux

/-- An actual generated queue origin obtains its abstract container spine
from the native auxiliary-validation result and the exact lowering run.  The
parameter-context conversion is the one derived by
`auxiliaryCanonicalParameterContext`; it is not selected by a caller. -/
theorem FinalLoweredGeneratedFamilyOrigin.abstractContainerApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (hempty : initialState.nestedAux = #[])
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations envCtors c.lparams
      result selection)
    (Horigin : FinalLoweredGeneratedFamilyOrigin c.env result.params nparams
      finalState target) :
    let parameterDomains :=
      (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse
    ∃ (realization : RestoredFamilyRealization envCtors
        c.lparams parameterDomains 0
        ((mkAppRange
          (.const Horigin.generated.sourceName Horigin.generated.levels)
          0 Horigin.generated.nestedNParams Horigin.generated.args).
            abstractList Horigin.generated.selection.fvars))
      abstractLevels baseArgs,
      Horigin.generated.levels.mapM
          (VLevel.ofLevel c.lparams) =
        some abstractLevels ∧
      baseArgs.length = Horigin.generated.nestedNParams ∧
      List.Forall₂
        (TrExprS envCtors c.lparams
          (abstractForallContext parameterDomains []))
        ((Horigin.generated.args.toList.take
          Horigin.generated.nestedNParams).map
            (fun arg =>
              arg.abstractList Horigin.generated.selection.fvars))
        baseArgs ∧
      (∀ arg ∈ baseArgs, arg.ClosedN parameterDomains.length) ∧
      realization.semantics.family = VExpr.mkApps
        (.const Horigin.generated.sourceName abstractLevels) baseArgs := by
  dsimp only
  let Hclosed : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have hselectionNodup : selection.fvars.Nodup :=
    Hclosed.selectionNodup selection
  have hsourceVEnvWF : sourceVEnv.WF := by
    have hwf := Hheaders.sourceContext.checking.tr.wf
    rw [Hheaders.sourceContextVEnv] at hwf
    exact hwf
  have henvCtorsWF : envCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource
      hsourceVEnvWF
  have Hcontexts : ∀ Haux : ClosedNestedAuxiliaryTranslation envCtors
      c.lparams result selection Horigin.generated.data.nested,
      VEnv.IsDefEqCtx envCtors c.lparams.length []
        ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse).reverse
        Haux.domains.reverse := by
    intro Haux
    exact Hclosed.auxiliaryFormationParameterContext Hsource hempty
      selection Haux
  rcases Horigin.generated.cachedFamilyRestoredRealizationZero Hmap
      hselectionNodup Htranslations henvCtorsWF
      ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse)
      Hcontexts with
    ⟨realization⟩
  rcases Horigin.generated.abstractContainerApplication realization
      henvCtorsWF (by
        have Hwf :=
          (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
            (elimLevel := .zero) (by trivial)).parameterWF.toCtx
        simpa using Hwf) with
    ⟨abstractLevels, baseArgs, Hlevels, hbaseLength, Hbase, HbaseClosed,
      hfamily⟩
  exact ⟨realization, abstractLevels, baseArgs, Hlevels, hbaseLength, Hbase,
    HbaseClosed, hfamily⟩

end VerifyInductive
end Lean4Lean
