import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Typing.RawShape

/-! The checked common-parameter prefix of each constructor determines its raw
syntactic shape (`CheckedConstructors.rawShapes`,
`CheckedConstructors.parameterShapes`) without inverting definitional
equality between forall types. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Exact raw translation state corresponding to a successful constructor
parameter prefix.  `rawScope` uses the domains selected by the structural
translation of the source constructor, while the executable's scope
uses the cached mutual parameters.  Keeping their pointwise local-context
conversion is what avoids forall injectivity. -/
def CheckedConstructorParameterPrefix.RawTranslation
    (_H : CheckedConstructorParameterPrefix env Us stats original
      i current checkedScope checkedDomains)
    (target : VExpr) : Prop :=
  ∃ rawScope domains residual,
    target = VExpr.wrapForalls domains residual ∧
    domains.length = i ∧
    rawScope.toCtx = domains.reverse ∧
    VLCtx.IsDefEq env Us.length rawScope checkedScope ∧
    TrExprS.IsUniqueCtx rawScope checkedScope ∧
    TrExprS env Us rawScope current residual

/-- Build the raw translation state directly from the exact structural
translation and the successful executable comparisons.  At each step
the two translations of the same concrete domain are compared directly;
the proof never inverts definitional equality between forall expressions. -/
theorem CheckedConstructorParameterPrefix.rawTranslation
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current checkedScope checkedDomains)
    (hscope : checkedScope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original target) :
    H.RawTranslation target := by
  induction H generalizing target with
  | zero =>
    exact ⟨[], [], target, by simp [VExpr.wrapForalls], rfl, rfl, .nil, .base,
      by simpa using Horiginal⟩
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    rename_i i name dom body bi oldScope sourceDomains param fv sourceDomain
      paramType deps
    rcases ih hscope.1 Horiginal with
      ⟨rawScope, domains, residual, htarget, hlength, hrawContext,
        Hcontexts, Hunique, Hcurrent⟩
    cases Hcurrent with
    | @forallE rawDomain rawBody _ _ _ _ _ rawDomainType rawBodyType
        rawDomainTranslation rawBodyTranslation =>
      have hrawSource := rawDomainTranslation.uniq henv Hcontexts hdomain
      have hsourceDomainTypeRaw := hdomainType.defeqDFC henv.ordered
        (Hcontexts.symm henv.orderedStrong).defeqCtx
      have hcompareRaw := hcompare.defeqDFC henv.ordered
        (Hcontexts.symm henv.orderedStrong).defeqCtx
      have hrawSourceAtSort := hrawSource.of_r henv Hcontexts.wf.toCtx
        (Classical.choose_spec hsourceDomainTypeRaw)
      have hcompareAtSort := hcompareRaw.of_l henv Hcontexts.wf.toCtx
        (Classical.choose_spec hsourceDomainTypeRaw)
      have hrawParam := hrawSourceAtSort.trans hcompareAtSort
      have hrawFresh : ∀ currentFv currentDeps,
          some (fv, deps) = some (currentFv, currentDeps) →
          currentFv ∉ rawScope.fvars ∧ currentDeps ⊆ rawScope.fvars := by
        intro currentFv currentDeps heq
        cases heq
        have hcheckedFresh := hscope.2.1 fv deps rfl
        simpa [Hcontexts.fvars] using hcheckedFresh
      let Hcontexts : VLCtx.IsDefEq env Us.length
          ((some (fv, deps), .vlam rawDomain) :: rawScope)
          ((some (fv, deps), .vlam paramType) :: oldScope) :=
        .cons Hcontexts hrawFresh (.vlam hrawParam)
      have Hopened := rawBodyTranslation.inst_fvar henv.orderedStrong Hcontexts.wf
      refine ⟨(some (fv, deps), .vlam rawDomain) :: rawScope,
        domains ++ [rawDomain], rawBody, ?_, ?_, ?_, Hcontexts,
        Hunique.cons .vlam, ?_⟩
      · rw [htarget]
        simp [VExpr.wrapForalls]
      · simp [hlength]
      · simp [VLCtx.toCtx, hrawContext, List.reverse_append]
      · simpa [Expr.instantiate1_eq, hparamFVar] using Hopened

/-- Package the exact raw-prefix translation state in the independent formation
judgment. -/
theorem CheckedConstructorParameterPrefix.ctorParameterShape
    {decl : VInductDecl} {ctor : VConstVal} {params : List VExpr}
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      decl.nparams current scope checkedDomains)
    (hscope : scope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original ctor.type)
    (huvars : decl.uvars = Us.length)
    (hparams : env.IsDefEqCtx Us.length [] params.reverse scope.toCtx) :
    decl.CtorParameterShape env params ctor := by
  rcases H.rawTranslation henv hscope Horiginal with
    ⟨rawScope, domains, residual, htarget, hlength, hrawContext,
      Hcontexts, _, _⟩
  refine ⟨domains, residual, ?_, ?_⟩
  · rw [htarget, ← hlength]
    exact VExpr.takeForalls_wrapForalls domains residual
  · have hrawChecked : env.IsDefEqCtx Us.length [] domains.reverse
        scope.toCtx := by
      rw [← hrawContext]
      exact Hcontexts.defeqCtx
    have hparams' := VEnv.IsDefEqCtx.trans_empty henv hparams
      (hrawChecked.symm henv.ordered)
    simpa [VInductDecl.ParamsDefEq, huvars] using hparams'

/-- The closed raw constructor retains the checked tail's telescope, owning
family, and common-parameter variables. Projection implementation choices
inside fields and indices do not affect this skeleton. -/
theorem CheckedConstructorParameterPrefix.rawCtorShape
    {decl : VInductDecl} {target : VInductiveType} {ctor : VConstVal}
    {tail : Expr} {tailTarget : VExpr}
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      decl.nparams tail scope sourceDomains)
    (hscope : scope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original ctor.type)
    (Htail : TrExprS env Us scope tail tailTarget)
    (Hcert : ConstructorTailCertificate env decl target scope.toCtx 0
      tailTarget classes) :
    decl.RawCtorShape target ctor := by
  rcases H.rawTranslation henv hscope Horiginal with
    ⟨rawScope, domains, residual, htarget, hlength, _, _, Hunique, Hresidual⟩
  have hres := TrExprS.rawShape Hunique.rawShape Hresidual Htail
  rcases Hcert.raw with ⟨doms, result, hwrap, hvalid, hhead⟩
  have hshape : decl.RawCtorShape target
      {ctor with type := VExpr.wrapForalls domains tailTarget} := by
    refine ⟨domains ++ doms, result, ?_, ?_, ?_, hhead⟩
    · simp only [hwrap, VExpr.wrapForalls_append]
    · simp [hlength]
    · simpa [hlength] using hvalid.raw
  apply hshape.of_rawShapeRel
  change VExpr.RawShapeRel ctor.type (VExpr.wrapForalls domains tailTarget)
  rw [htarget]
  exact hres.wrapForalls domains

end VerifyInductive
end Lean4Lean
