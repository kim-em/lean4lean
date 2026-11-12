import Lean4Lean.Verify.Typing.Translation
import Lean4Lean.Verify.Typing.VLCtxLemmas
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.ExprUniverses

/-! Universe substitution in translations, used to drop the recursor's elimination universe.

`TrExprS.substLevelParamsCore` instantiates the universe parameters of a translated term
with the executable's non-reducing level substitution. Its instance
`TrExprS.dropFreshLevelParam` replaces the extra elimination universe of a recursor
context by zero and leaves the declaration's universe parameters unchanged, which brings a
translation over the recursor's universe parameters back to the declaration's. -/

namespace Lean4Lean
open Lean hiding Environment Exception

/-- Replace the extra elimination universe `fresh` by zero and leave every other universe
parameter unchanged. -/
def recursorDropLevel (fresh : Name) (name : Name) : Level :=
  if name = fresh then .zero else .param name

def recursorDropLevels (n : Nat) : List VLevel := .zero :: VLevel.params n

theorem levelParamsIn_fixed_dropFresh {e : Expr}
    (H : e.levelParamsIn Us = true) (hfresh : fresh ∉ Us) :
    Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e = e := by
  apply Expr.levelParamsIn_subst_fixed H
  intro name hname
  simp [recursorDropLevel, show name ≠ fresh from fun heq => hfresh (heq ▸ hname)]

theorem recursorDropLevels_wf : ∀ level ∈ recursorDropLevels n, level.WF n := by
  simp only [recursorDropLevels, List.mem_cons, forall_eq_or_imp]
  exact ⟨True.intro, fun _ h => VLevel.params_wf h⟩

theorem ofLevel_dropFresh
    (H : VLevel.ofLevel (fresh :: Us) u = some u') :
    VLevel.ofLevel Us (u.substParams' (recursorDropLevel fresh) false) =
      some (u'.inst (recursorDropLevels Us.length)) := by
  induction u generalizing u' with
  | zero =>
    simp only [VLevel.ofLevel] at H
    cases H
    rfl
  | succ u ih =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨target, htarget, ⟨⟩⟩ := Option.bind_eq_some_iff.mp H
    simpa [Level.substParams', VLevel.ofLevel, VLevel.inst] using ih htarget
  | max left right ihLeft ihRight | imax left right ihLeft ihRight =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨leftTarget, hleft, hrest⟩ := Option.bind_eq_some_iff.mp H
    obtain ⟨rightTarget, hright, ⟨⟩⟩ := Option.bind_eq_some_iff.mp hrest
    simp [Level.substParams', VLevel.ofLevel, VLevel.inst, ihLeft hleft, ihRight hright]
  | param name =>
    by_cases heq : name = fresh
    · subst name
      simp [VLevel.ofLevel] at H
      cases H
      simp [Level.substParams', recursorDropLevel, recursorDropLevels, VLevel.ofLevel, VLevel.inst]
    · have hbeq : (fresh == name) = false := by
        simp [show fresh ≠ name from Ne.symm heq]
      simp [VLevel.ofLevel, List.idxOf_cons, hbeq] at H
      obtain ⟨hindex, rfl⟩ := H
      simp [Level.substParams', recursorDropLevel, heq, VLevel.ofLevel, hindex,
        VLevel.inst, recursorDropLevels, VLevel.params, List.getD_eq_getElem?_getD]
  | mvar => simp [VLevel.ofLevel] at H

theorem TrExprS.dropFreshLevelParam
    (hΔ : VLCtx.WF env (fresh :: Us).length Δ)
    (H : TrExprS env (fresh :: Us) Δ e e') :
    TrExprS env Us (Δ.instL (recursorDropLevels Us.length))
      (Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e)
      (e'.instL (recursorDropLevels Us.length)) :=
  H.substLevelParamsCore hΔ recursorDropLevels_wf
    (fun _ _ hu => ofLevel_dropFresh hu)

theorem recursorDropLevels_prependShift :
    (VLevel.prependShift n).map (VLevel.inst (recursorDropLevels n)) = VLevel.params n := by
  simp only [VLevel.prependShift, VLevel.params, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  simp [VLevel.inst, recursorDropLevels, VLevel.params,
    List.getD_eq_getElem?_getD, hi']

theorem VLCtx.WF.prepend_drop_levels (H : VLCtx.WF env U Δ) :
    (Δ.instL (VLevel.prependShift U)).instL (recursorDropLevels U) = Δ := by
  rw [VLCtx.instL_instL, recursorDropLevels_prependShift, H.instL_id]

end Lean4Lean
