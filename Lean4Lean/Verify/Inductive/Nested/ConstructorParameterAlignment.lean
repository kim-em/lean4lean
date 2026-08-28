import Lean4Lean.Verify.Inductive.Recursor.Structure
import Lean4Lean.Verify.Inductive.Nested.Opening
import Lean4Lean.Verify.Inductive.Nested.OriginalHeaderSeedRebase
import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Proof-relevant dependencies of precisely the derivations retained by one
successful executable constructor-parameter replay. -/
inductive CheckedConstructorParameterPrefix.UsesOnly
    (changed : Name → Prop) :
    ∀ {env Us stats original i current scope sourceDomains}
      (H : CheckedConstructorParameterPrefix env Us stats original
        i current scope sourceDomains), Prop where
  | zero : UsesOnly changed
      (CheckedConstructorParameterPrefix.zero (env := env) (Us := Us)
        (stats := stats) (original := original))
  | step
      (Huses : H.UsesOnly changed)
      (hdomainUses : hdomain.UsesOnly changed)
      (hdomainTypeUses : hdomainType.UsesOnly changed)
      (hcompareUses : hcompare.UsesOnly changed) :
      UsesOnly changed
        (CheckedConstructorParameterPrefix.step H hparam hparamFVar
          hdomain hdomainType hcompare)

/-- Rebase every retained translation, typehood derivation, and executable
comparison in an exact restricted parameter replay. -/
theorem CheckedConstructorParameterPrefix.rebaseExcept
    (E : VEnv.LEExcept changed src dst)
    (H : CheckedConstructorParameterPrefix src Us stats original
      i current scope sourceDomains)
    (HU : H.UsesOnly changed) :
    CheckedConstructorParameterPrefix dst Us stats original
      i current scope sourceDomains := by
  induction HU with
  | zero => exact .zero
  | step Huses hdomainUses hdomainTypeUses hcompareUses ih =>
    apply CheckedConstructorParameterPrefix.step (ih E)
    · assumption
    · assumption
    · exact TrExprS.rebaseExcept E _ hdomainUses
    · exact VEnv.IsType.rebaseExcept E _ hdomainTypeUses
    · exact VEnv.IsDefEqU.rebaseExcept E _ hcompareUses

/-- A trace constructed where every available constant avoids `changed`
inherits restriction evidence pointwise. -/
theorem CheckedConstructorParameterPrefix.usesOnly_of_constants
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope sourceDomains)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) : H.UsesOnly changed := by
  induction H with
  | zero => exact .zero
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    exact .step (hparam := hparam) (hparamFVar := hparamFVar) ih
      (hdomain.usesOnly_of_constants Hconstants)
      (hdomainType.usesOnly_of_constants Hconstants)
      (hcompare.usesOnly_of_constants Hconstants)

/-- The narrow executable-locality seam for constructor parameters.  It is
stated entirely at the ordinary producer boundary: the exact replay proof
returned for an exact family/constructor position must not consult the
freshly installed declaration names. -/
def ConstructorParameterReplayLocality : Prop :=
  ∀ {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length)
    {tail : Expr} {sourceDomains : List VExpr}
    (Hchecked : CheckedConstructorParameterPrefix H.context.venv c.lparams
      stats indTypes[familyIdx].ctors[ctorIdx].type stats.params.size tail
      H.materialized.parameterScope sourceDomains),
    Hchecked.UsesOnly (fun name => name ∈ decl.sourceNames)

/-- A lowered post-header environment embeds into an independently checked
source post-constructor environment away from the lowered declaration's own
names.  Starting at the post-header boundary lets an exact executable
parameter replay be rebased without first weakening its proof. -/
theorem TrInductDeclCore.typeEnvToCtorEnvLEExcept
    (Hfrom : TrInductDeclCore base fromLparams fromNparams fromTypes
      fromUnsafe fromDecl fromEnvTypes fromEnvCtors)
    (Hto : TrInductDeclCore base toLparams toNparams toTypes
      toUnsafe toDecl toEnvTypes toEnvCtors) :
    VEnv.LEExcept (fun name => name ∈ fromDecl.sourceNames)
      fromEnvTypes toEnvCtors := by
  have HtoAdded : base.addConstVals
      (toDecl.typeConstants ++ toDecl.constructorConstants) =
      some toEnvCtors :=
    VEnv.addConstVals_append Hto.typesAdded Hto.ctorsAdded
  apply VEnv.addConstVals_LEExcept Hfrom.typesAdded HtoAdded
  intro ci hci
  unfold VInductDecl.sourceNames
  exact List.mem_append_left _ (List.mem_map.mpr ⟨ci, hci, rfl⟩)

/-- Transport a full translation across definitionally equal local contexts
without changing its chosen target.  `TrExprS.defeqDFC` supplies a new
structural target; uniqueness relates that target back to the exact target
carried by `TrExpr`. -/
theorem TrExpr.defeqDFCExact
    (henv : env.WF)
    (hctx : VLCtx.IsDefEq env Us.length sourceCtx targetCtx)
    (H : TrExpr env Us sourceCtx source target) :
    TrExpr env Us targetCtx source target := by
  rcases H with ⟨translated, Htranslated, htarget⟩
  rcases Htranslated.defeqDFC henv hctx with
    ⟨translated', Htranslated'⟩
  have htranslated := Htranslated.uniq henv hctx Htranslated'
  exact ⟨translated', Htranslated',
    (htranslated.symm.trans henv hctx.wf.toCtx htarget).defeqDFC
      henv hctx.defeqCtx⟩

/-- Open one anonymous translated binder with the exact cached free
variable while retaining the target chosen by a full translation. -/
theorem TrExpr.instFVarExact
    (henv : env.Ordered)
    (hscope : VLCtx.WF env Us.length
      ((some (fv, deps), decl) :: scope))
    (H : TrExpr env Us ((none, decl) :: scope) body target) :
    TrExpr env Us ((some (fv, deps), decl) :: scope)
      (body.instantiate1' (.fvar fv)) target := by
  rcases H with ⟨translated, Htranslated, htarget⟩
  refine ⟨translated, Htranslated.inst_fvar henv hscope, ?_⟩
  cases decl <;> simpa [VLCtx.toCtx] using htarget

/-- Replay an exact checked constructor-parameter prefix against an
independently chosen translation of the original constructor type.

Besides reconstructing the successively opened residual as a full
translation in the cached parameter scope, the theorem identifies the exact
translated prefix domains with that scope by dependent definitional
equality.  This is the operational bridge needed after nested restoration:
the translated constructor domains need not be syntactically equal to the
family parameter domains. -/
theorem CheckedConstructorParameterPrefix.alignmentOfTranslation
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope checkedDomains)
    (hscope : VLCtx.WF env Us.length scope)
    (Horiginal : TrExpr env Us [] original
      (VExpr.wrapForalls actualDomains residual))
    (hlength : actualDomains.length = i) :
    env.IsDefEqCtx Us.length [] actualDomains.reverse scope.toCtx ∧
      TrExpr env Us scope current residual := by
  induction H generalizing actualDomains residual with
  | zero =>
    have hdomains : actualDomains = [] :=
      List.eq_nil_of_length_eq_zero hlength
    subst actualDomains
    exact ⟨.zero, by simpa [VExpr.wrapForalls] using Horiginal⟩
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    rename_i i name dom body bi scope sourceDomains param fv sourceDomain
      paramType deps
    have hdomainsNe : actualDomains ≠ [] := by
      intro heq
      subst actualDomains
      simp at hlength
    let actualPrefix := actualDomains.dropLast
    let actualDomain := actualDomains.getLast hdomainsNe
    have hdomains : actualPrefix ++ [actualDomain] = actualDomains :=
      List.dropLast_concat_getLast hdomainsNe
    have Horiginal' : TrExpr env Us [] original
        (VExpr.wrapForalls actualPrefix (.forallE actualDomain residual)) := by
      rw [← hdomains] at Horiginal
      simpa [VExpr.wrapForalls_append, VExpr.wrapForalls] using Horiginal
    rcases ih hscope.1 Horiginal' (by
      have hlength' := hlength
      rw [← hdomains] at hlength'
      simp at hlength'
      omega) with
      ⟨hprefixCtx, Hcurrent⟩
    rcases Hcurrent with ⟨currentTarget, HcurrentS, hcurrentTarget⟩
    cases HcurrentS with
    | @forallE generatedDomain generatedBody _ _ _ _ _
        hgeneratedDomainType hgeneratedBodyType
        hgeneratedDomain hgeneratedBody =>
      have hscopeRefl : VLCtx.IsDefEq env Us.length _ _ :=
          .refl henv.ordered hscope.1
      have hgeneratedSource :=
          hgeneratedDomain.uniq henv hscopeRefl hdomain
      have hcurrentInv := VEnv.IsDefEqU.forallE_inv henv
          hscope.1.toCtx hcurrentTarget
      rcases hcurrentInv.1 with ⟨domainLevel, hgeneratedActual⟩
      rcases hcurrentInv.2 with ⟨bodyLevel, hgeneratedBodyResidual⟩
      rcases hdomainType with ⟨sourceLevel, hsourceDomainType⟩
      have hgeneratedSourceAtSort := hgeneratedSource.of_r henv
        hscope.1.toCtx hsourceDomainType
      have hcompareAtSort := hcompare.of_l henv hscope.1.toCtx
        hsourceDomainType
      have hgeneratedParamAtSort :=
        hgeneratedSourceAtSort.trans hcompareAtSort
      have hactualParam := VEnv.IsDefEq.transU_r henv hscope.1.toCtx
        (show env.IsDefEqU Us.length _ actualDomain generatedDomain from
          ⟨.sort domainLevel, hgeneratedActual.symm⟩)
        hgeneratedParamAtSort
      have hactualParamAtPrefix :=
          hactualParam.defeqDFC henv.ordered
            (hprefixCtx.symm henv.ordered)
      have hcontexts := VEnv.IsDefEqCtx.succ hprefixCtx
          hactualParamAtPrefix
      let hbodyTranslation : TrExpr env Us
            ((none, .vlam generatedDomain) :: _) _ residual :=
          ⟨generatedBody, hgeneratedBody,
            ⟨.sort bodyLevel, hgeneratedBodyResidual⟩⟩
      have hbodyCtx := VLCtx.IsDefEq.cons (ofv := none) hscopeRefl nofun
          (.vlam hgeneratedParamAtSort)
      have hbodyTranslation' := TrExpr.defeqDFCExact henv hbodyCtx
          hbodyTranslation
      have hopened := TrExpr.instFVarExact henv.ordered hscope
          hbodyTranslation'
      refine ⟨?_, ?_⟩
      · rw [← hdomains]
        simpa [List.reverse_append, VLCtx.toCtx] using hcontexts
      · simpa [Expr.instantiate1_eq, hparamFVar] using hopened

/-- Transfer an exact checked parameter trace to another constructor source
with the same concrete forall prefix.  The generalized `remaining` index is
the key induction invariant: after the checked trace has consumed `i`
binders, the two opened residuals still share exactly `remaining` binders.

No translation of either residual is involved.  In particular, this applies
when nested lowering preserves the parameter telescope but replaces the
constructor result below it. -/
theorem CheckedConstructorParameterPrefix.transferSameForallPrefix
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope checkedDomains)
    (Hsame : Expr.SameForallPrefix (i + remaining)
      sourceOriginal original) :
    ∃ sourceCurrent,
      CheckedConstructorParameterPrefix env Us stats sourceOriginal
        i sourceCurrent scope checkedDomains ∧
      Expr.SameForallPrefix remaining sourceCurrent current := by
  induction H generalizing sourceOriginal remaining with
  | zero =>
    exact ⟨sourceOriginal, .zero, by simpa using Hsame⟩
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    rename_i i name dom body bi scope sourceDomains param fv sourceDomain
      paramType deps
    have Hsame' : Expr.SameForallPrefix (i + (remaining + 1))
        sourceOriginal original := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hsame
    rcases ih Hsame' with
      ⟨sourceCurrent, Hsource, Hremaining⟩
    cases Hremaining with
    | @cons _ sourceBody _ _ _ _ Hbody =>
      refine ⟨sourceBody.instantiate1 param,
        .step Hsource hparam hparamFVar hdomain hdomainType hcompare, ?_⟩
      simpa [Expr.instantiate1_eq] using Hbody.instantiate1' param

/-- Compare the exact translated parameter domains of an independently
translated source constructor with the cached family-parameter scope used by
constructor checking, when nested lowering changed only the residual below
that common prefix.

This is the source-facing form of `alignmentOfTranslation`: the checked trace
is first transported across the concrete prefix equality, so the lowered
residual is never translated in the restored environment. -/
theorem CheckedConstructorParameterPrefix.contextDefEqOfSameForallPrefixTranslation
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope checkedDomains)
    (hscope : VLCtx.WF env Us.length scope)
    (Hsame : Expr.SameForallPrefix i sourceOriginal original)
    (Hsource : TrExpr env Us [] sourceOriginal
      (VExpr.wrapForalls sourceDomains sourceResidual))
    (hlength : sourceDomains.length = i) :
    env.IsDefEqCtx Us.length [] sourceDomains.reverse scope.toCtx := by
  rcases H.transferSameForallPrefix
      (remaining := 0) (by simpa using Hsame) with
    ⟨sourceCurrent, HsourceChecked, _⟩
  exact (HsourceChecked.alignmentOfTranslation henv hscope Hsource
    hlength).1

end VerifyInductive
end Lean4Lean
