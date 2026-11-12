import Lean4Lean.Verify.Expr.SameForallPrefix
import Lean4Lean.Verify.Inductive.Recursor.Installation

/-! Identical concrete forall prefixes (`Expr.SameForallPrefix`) and the closing of two bodies
over the same local selection (`CDeclArray.sameForallPrefix`), used by the rule typing. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive


/-- A positional free-variable declaration (`FVarDeclAt`) and a declaration occurring at the
same free-variable identifier in a well-formed context are the same local
declaration. -/
theorem FVarDeclAt.declaration_eq_of_mem
    (D : FVarDeclAt c xs i)
    (Hc : BindingContextWF c)
    (d : LocalDecl) (hd : d ∈ c.lctx.toList)
    (hfv : d.fvarId = D.fvar) :
    d = .cdecl D.index D.fvar D.userName D.type D.binderInfo D.kind := by
  have hfind := Lean.LocalContext.WF.find?_eq_some_of_mem Hc.wf hd
  rw [hfv] at hfind
  exact Option.some.inj (hfind.symm.trans D.declaration)



/-- Two translated forall telescopes with the same concrete prefix and the same
residual source are definitionally equal, at a sort level, so that a dependent
context conversion can be extended by the resulting domain. -/
theorem Expr.SameForallPrefix.translatedWholeTargetsOfResidualRightSort
    (H : Expr.SameForallPrefix n leftSource rightSource)
    (henv : VEnv.WF env)
    (Hbase : VEnv.IsDefEqCtx env Us.length []
      baseLeft.reverse baseRight.reverse)
    (Hleft : TrExprS env Us
      (abstractForallContext baseLeft []) leftSource
      (VExpr.wrapForalls leftDomains leftTarget))
    (Hright : TrExprS env Us
      (abstractForallContext baseRight []) rightSource
      (VExpr.wrapForalls rightDomains rightTarget))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n)
    (HleftResidual : TrExprS env Us
      (abstractForallContext (baseLeft ++ leftDomains) []) residualSource
      leftTarget)
    (HrightResidual : TrExprS env Us
      (abstractForallContext (baseRight ++ rightDomains) []) residualSource
      rightTarget)
    (HrightResidualType : env.IsType Us.length
      (abstractForallContext (baseRight ++ rightDomains) []).toCtx
      rightTarget) :
    ∃ level, env.IsDefEq Us.length baseLeft.reverse
      (VExpr.wrapForalls leftDomains leftTarget)
      (VExpr.wrapForalls rightDomains rightTarget) (.sort level) := by
  have HbaseV := abstractForallContext.isDefEq Hbase
  have Hlocals := H.translatedContextsExact henv HbaseV Hleft Hright
    hleftLength hrightLength
  have Hlocals' : VEnv.IsDefEqCtx env Us.length []
      (baseLeft ++ leftDomains).reverse
      (baseRight ++ rightDomains).reverse := by
    simpa [List.reverse_append, VLCtx.toCtx] using Hlocals
  have HresidualU := TrExprS.uniqAbstractForallContext
    HleftResidual HrightResidual henv Hlocals'
  rcases HrightResidualType with ⟨residualLevel, HrightResidualType⟩
  have HrightResidualType' : env.HasType Us.length
      (baseRight ++ rightDomains).reverse rightTarget
      (.sort residualLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      HrightResidualType
  have HrightResidualTypeLeft : env.HasType Us.length
      (baseLeft ++ leftDomains).reverse rightTarget
      (.sort residualLevel) :=
    HrightResidualType'.defeqDFC henv.ordered
      (Hlocals'.symm henv.ordered)
  have Hresidual : env.IsDefEq Us.length
      (baseLeft ++ leftDomains).reverse leftTarget rightTarget
      (.sort residualLevel) :=
    HresidualU.of_r henv Hlocals'.isType HrightResidualTypeLeft
  have Hclosed :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hlocals'
      n (by simp [hleftLength]) Hresidual
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  exact ⟨closedLevel, by
    simpa [hleftLength, hrightLength] using Hclosed⟩

/-- Closing two bodies over the same duplicate-free local selection gives
the same concrete forall prefix, independently of the bodies. -/
theorem CDeclArray.sameForallPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameForallPrefix xs.size
      (lctx.mkForall xs left) (lctx.mkForall xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallPrefixN_fold hdecl left right


end VerifyInductive
end Lean4Lean
