import Lean4Lean.Verify.Inductive.Nested.FamilyRealization
import Lean4Lean.Verify.Inductive.Nested.Mapping
import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Producer-owned generated-family header evidence -/

/-- The validated translation of a generated family's cached source
application exposes the exact abstract container application and an ordered
translation of every specialized parameter.  In particular, the abstract
arguments are closed in precisely the common-parameter context; no
constructor-field binder can occur in them.

This is the source spine needed both to construct the canonical direct
auxiliary family and, after weakening, to interpret an actual lowering hit.
-/
theorem GeneratedFamilyWitness.abstractContainerApplication
    (H : GeneratedFamilyWitness prodEnv params nestedAux family)
    (R : RestoredFamilyRealization venv lparams parameterDomains 0
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars))
    (henv : venv.WF)
    (hparams : OnCtx parameterDomains.reverse
      (venv.IsType lparams.length)) :
    ∃ abstractLevels baseArgs,
      H.levels.mapM (VLevel.ofLevel lparams) = some abstractLevels ∧
      baseArgs.length = H.nestedNParams ∧
      List.Forall₂
        (TrExprS venv lparams
          (abstractForallContext parameterDomains []))
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars))
        baseArgs ∧
      (∀ arg ∈ baseArgs, arg.ClosedN parameterDomains.length) ∧
      R.semantics.family = VExpr.mkApps
        (.const H.sourceName abstractLevels) baseArgs := by
  have hsourceApp :
      mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams H.args =
        Expr.mkAppList (.const H.sourceName H.levels)
          (H.args.toList.take H.nestedNParams) := by
    apply Expr.mkAppRange_eq
        (l₁ := []) (l₂ := H.args.toList.take H.nestedNParams)
        (l₃ := H.args.toList.drop H.nestedNParams)
    · simp
    · rfl
    · simpa using Nat.min_eq_left H.argsArity
  have habstractApp :
      (Expr.mkAppList (.const H.sourceName H.levels)
        (H.args.toList.take H.nestedNParams)).abstractList
          H.selection.fvars =
        Expr.mkAppList (.const H.sourceName H.levels)
          ((H.args.toList.take H.nestedNParams).map
            (fun arg => arg.abstractList H.selection.fvars)) := by
    have go : ∀ (args : List Expr) (head : Expr),
        (Expr.mkAppList head args).abstractList H.selection.fvars =
          Expr.mkAppList (head.abstractList H.selection.fvars)
            (args.map (fun arg => arg.abstractList H.selection.fvars)) := by
      intro args
      induction args with
      | nil => simp
      | cons arg args ih =>
        intro head
        simp [Expr.mkAppList, Expr.abstractList_app, ih]
    simpa using go (H.args.toList.take H.nestedNParams)
      (.const H.sourceName H.levels)
  let targetFamily : VExpr := R.semantics.family
  have Htranslated : TrExprS venv lparams
      (abstractForallContext parameterDomains [])
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars) targetFamily :=
    R.sourceTranslation
  rw [hsourceApp, habstractApp] at Htranslated
  rcases checkPositivityStep.TrExprS.mkAppList_inv Htranslated with
    ⟨abstractHead, baseArgs, Hhead, HbaseArgs, hfamily⟩
  have hvlctxWF :
      (abstractForallContext parameterDomains []).WF venv lparams.length := by
    have go : ∀ domains : List VExpr,
        OnCtx domains (venv.IsType lparams.length) →
        VLCtx.WF venv lparams.length
          (domains.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) := by
      intro domains Hdomains
      induction domains with
      | nil => trivial
      | cons domain domains ih =>
        have Hdomain : venv.IsType lparams.length
            (VLCtx.toCtx (domains.map fun type =>
              ((none, .vlam type) :
                Option (FVarId × List FVarId) × VLocalDecl))) domain := by
          rw [VLCtx.toCtx_map_anonymousLams]
          exact Hdomains.2
        exact ⟨ih Hdomains.1, nofun, Hdomain⟩
    simpa [abstractForallContext] using go parameterDomains.reverse hparams
  cases Hhead with
  | const _ hlevels _ =>
    refine ⟨_, baseArgs, hlevels, ?_, HbaseArgs, ?_, ?_⟩
    · have hlength := Lean4Lean.List.Forall₂.length_eq HbaseArgs
      simpa using hlength.symm.trans (by
        simp [Nat.min_eq_left H.argsArity])
    · intro arg harg
      rcases Lean4Lean.List.Forall₂.forall_exists_r HbaseArgs arg harg with
        ⟨sourceArg, _hsourceArg, Harg⟩
      have HargWF := Harg.wf henv.ordered hvlctxWF
      have hctxClosed : CtxClosed
          (abstractForallContext parameterDomains []).toCtx := by
        simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
          VEnv.CtxWF.closed henv.ordered hparams
      have Hclosed := HargWF.closedN henv.ordered hctxClosed
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hclosed
    · simpa [targetFamily] using hfamily

end VerifyInductive
end Lean4Lean
