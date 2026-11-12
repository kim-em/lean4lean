import Lean4Lean.Verify.Inductive.Header.Block

/-!
# Checked header translations

Upgrades the raw header translations of `Header/RawTranslation.lean` to `TrSourceConst`
once the header telescope and result sort have been checked (the `ClosedHeaderCheck.checked*`
lemmas for the terminal, first and later forall-headed cases).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace TrSourceConstRaw

/-- Upgrade a raw source translation once an independently checked,
definitionally equal presentation is known to be a type. -/
theorem checkedOfDefEqType
    (H : TrSourceConstRaw env Us name type target)
    (henv : env.WF)
    (hdefeq : env.IsDefEqU Us.length [] target.type normalized)
    (hnormalized : env.IsType Us.length [] normalized) :
    TrSourceConst env Us name type target := by
  refine {
    uvars := H.uvars
    name := H.name
    type := H.type
    wf := ?_ }
  change env.IsType target.uvars [] target.type
  rw [H.uvars]
  exact hnormalized.defeqU_l henv (by trivial) hdefeq.symm

/-- A strict translation of a syntactic forall carries exactly the domain
and codomain `IsType` witnesses needed to discharge raw header formation. -/
theorem checkedOfForallTranslation
    (H : TrSourceConstRaw env Us name type target)
    (henv : env.WF)
    (hdefeq : env.IsDefEqU Us.length [] target.type normalized)
    (hforall : TrExprS env Us [] (.forallE binderName domain body binderInfo)
      normalized) :
    TrSourceConst env Us name type target := by
  cases hforall with
  | forallE hdomain hbody _ _ =>
    exact checkedOfDefEqType H henv hdefeq
      (VEnv.IsType.forallE hdomain hbody)

end TrSourceConstRaw

namespace checkInductiveTypes.loopType

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

/-- At the terminal `loopType` continuation the checker context is empty, so
the `ensureSort` result and the closed normal-form translation live in
the same empty context.  Uniqueness of translation then shows the raw target
is a type, which upgrades the raw translation to `TrSourceConst` in the
non-forall (zero remaining arity) case. -/
theorem ClosedHeaderCheck.checkedTerminal
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    {normalized : Expr} {type₀ : VExpr}
    (H : ClosedHeaderCheck Hc source.name source.type
      checkedType)
    (hclosed : TrExpr Hc.venv c.lparams [] normalized H.target.type)
    (htype₀ : TrExprS Hc.venv c.lparams [] normalized type₀)
    (hsort : TrExpr Hc.venv c.lparams [] (.sort resultSort) type₀) :
    ∃ resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel ∧
      TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  rcases TrExpr.sort_result (Δ := []) Hc.checking.tr.wf (by trivial) hsort with
    ⟨resultLevel, hofLevel, hsorted⟩
  rcases hclosed with ⟨closed, hclosedS, hclosedEq⟩
  have hclosedType := hclosedS.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf (by trivial)) htype₀
  have hdefeq : Hc.venv.IsDefEqU c.lparams.length [] H.target.type type₀ :=
    hclosedEq.symm.trans Hc.checking.tr.wf (by trivial) hclosedType
  have htarget := TrSourceConstRaw.checkedOfDefEqType H.source
    Hc.checking.tr.wf hdefeq
    ⟨_, hsorted.hasType.1⟩
  exact ⟨resultLevel, hofLevel, htarget⟩

/-- A forall-headed first normal form is already type-valued by strict
translation, so its raw existential target can initialize the existing
header-synthesis recursion without assuming a skeleton from the caller. -/
theorem ClosedHeaderCheck.checkedFirstForall
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    (H : ClosedHeaderCheck Hc source.name source.type
      checkedType)
    (hctx : Hc.mlctx.vlctx = [])
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.forallE binderName domain body binderInfo) H.runtimeTarget) :
    TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  let target : VInductiveTypeSkeleton := {
    toVConstVal := H.target
    ctors := [] }
  rcases initialHeaderNormalization Hc hctx
      (target := target) H.source H.typing hnormalized with
    ⟨normalized, _exprType, hforall, hdefeq⟩
  have hforall' : TrExprS Hc.venv c.lparams []
      (.forallE binderName domain body binderInfo) normalized := by
    simpa [hctx] using hforall
  exact Lean4Lean.VerifyInductive.TrSourceConstRaw.checkedOfForallTranslation
    H.source Hc.checking.tr.wf
    hdefeq.toU hforall'

/-- Later forall-headed normal forms are translated in the empty checker
context by the closed `whnf`; their strict translation then upgrades the
corresponding raw target without importing ambient indices from earlier
mutual headers. -/
theorem ClosedHeaderCheck.checkedLaterForall
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    (H : ClosedHeaderCheck Hc source.name source.type
      checkedType)
    (hclosed : TrExpr Hc.venv c.lparams []
      (.forallE binderName domain body binderInfo) H.target.type) :
    TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  rcases hclosed with ⟨normalized, hforall, hdefeq⟩
  exact Lean4Lean.VerifyInductive.TrSourceConstRaw.checkedOfForallTranslation
    H.source Hc.checking.tr.wf
    hdefeq.symm hforall

end checkInductiveTypes.loopInd
end VerifyInductive
end Lean4Lean
