import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.ExprUniverses
namespace Lean4Lean
open Lean hiding Environment Exception

/-- Exact universe substitution for nonreducing native level replacement.
In particular, dropping an unused recursor universe must not simplify other
native universe expressions while reconstructing their strict translation. -/
theorem TrExprS.substLevelParamsCore
    (hΔ : VLCtx.WF env ps.length Δ)
    (hls : ∀ level ∈ ls, level.WF Us.length)
    (hlevels : ∀ u u', VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F false) = some (u'.inst ls))
    (H : TrExprS env ps Δ e e') :
    TrExprS env Us (Δ.instL ls) (Expr.instantiateLevelParamsCore' false F e)
      (e'.instL ls) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (hlevels _ _ hlevel)
  | @const _ _ sourceLevels targetLevels info hlookup hlevel harity =>
    apply TrExprS.const hlookup ?_ (by simpa using harity)
    have Hmap := List.mapM_eq_some.mp hlevel
    apply List.mapM_eq_some.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun u u' hu => hlevels u u' hu) Hmap
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hls)
      (VLCtx.instL_toCtx _ ▸ harg.instL hls) (ihFn hΔ) (ihArg hΔ)
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hls)
      (ihTy hΔ) (ihVal hΔ) (ihBody ⟨hΔ, nofun, hval⟩)
  | lit hlit _ ih =>
    exact .lit hlit (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ hproj ih =>
    exact .proj (ih hΔ) (VLCtx.instL_toCtx _ ▸ hproj.instL hls)

/-- Replace the extra elimination universe by zero, leaving source universe
syntax unchanged. This is used to choose a fresh original-universe witness;
it is not an assertion that the old witness omitted the extra universe. -/
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

private theorem OnCtx.typeLevelWF {env : VEnv}
    (H : OnCtx Γ (env.IsType U)) : OnCtx Γ (fun _ A => A.LevelWF U) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
    exact ⟨ih H.1, (Classical.choose_spec H.2).levelWF (ih H.1) |>.1⟩

theorem VLCtx.WF.instL_id (H : VLCtx.WF env U Δ) :
    Δ.instL (VLevel.params U) = Δ := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    have hctx := OnCtx.typeLevelWF H.1.toCtx
    have htail := ih H.1
    cases d with
    | vlam ty =>
      obtain ⟨level, htype⟩ := H.2.2
      have hlevels := (htype.levelWF hctx).1
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.instL_id]
    | vlet ty value =>
      have hlevels := H.2.2.levelWF hctx
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.1.instL_id, hlevels.2.2.instL_id]

theorem recursorDropLevels_prependShift :
    (VLevel.prependShift n).map (VLevel.inst (recursorDropLevels n)) = VLevel.params n := by
  simp only [VLevel.prependShift, VLevel.params, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  simp [VLevel.inst, recursorDropLevels, VLevel.params,
    List.getD_eq_getElem?_getD, hi']

theorem VLCtx.instL_instL {Δ : VLCtx} :
    (Δ.instL ls).instL ls' = Δ.instL (ls.map (VLevel.inst ls')) := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    cases d <;> simp [VLCtx.instL, VLocalDecl.instL, ih, VExpr.instL_instL]

theorem VLCtx.WF.prepend_drop_levels (H : VLCtx.WF env U Δ) :
    (Δ.instL (VLevel.prependShift U)).instL (recursorDropLevels U) = Δ := by
  rw [VLCtx.instL_instL, recursorDropLevels_prependShift, H.instL_id]

/-- Choose a strict original-universe translation by dropping the fresh
parameter, and lift that choice back exactly. Only source syntax is required
to omit the fresh name; projection metadata in the old target may mention it. -/
theorem TrExprS.chooseOriginalUniverses
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hfresh : fresh ∉ Us)
    (hsource : Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e = e)
    (H : TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e e') :
    ∃ sourceTarget,
      TrExprS env Us Δ e sourceTarget ∧
      TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e
        (sourceTarget.instL (VLevel.prependShift Us.length)) := by
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  have hctx := (show VLCtx.WF env (VLevel.prependShift Us.length).length Δ from by
    simpa using hΔ).instL hshift
  have Hdrop := H.dropFreshLevelParam (by simpa using hctx)
  rw [hsource, hΔ.prepend_drop_levels] at Hdrop
  exact ⟨_, Hdrop, Hdrop.prependLevelParam henv hΔ hfresh⟩

theorem ofLevel_fixed_dropFresh
    (hfresh : fresh ∉ Us) (H : VLevel.ofLevel Us u = some u') :
    u.substParams' (recursorDropLevel fresh) false = u := by
  induction u generalizing u' with
  | zero => rfl
  | succ u ih =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨target, htarget, ⟨⟩⟩ := Option.bind_eq_some_iff.mp H
    simp [Level.substParams', ih htarget]
  | max left right ihLeft ihRight | imax left right ihLeft ihRight =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨leftTarget, hleft, hrest⟩ := Option.bind_eq_some_iff.mp H
    obtain ⟨rightTarget, hright, ⟨⟩⟩ := Option.bind_eq_some_iff.mp hrest
    simp [Level.substParams', ihLeft hleft, ihRight hright]
  | param name =>
    have hmem : name ∈ Us := by
      simp only [VLevel.ofLevel, Option.ite_none_right_eq_some] at H
      exact List.idxOf_lt_length_iff.mp H.1
    have hne : name ≠ fresh := by intro heq; exact hfresh (heq ▸ hmem)
    simp [Level.substParams', recursorDropLevel, hne]
  | mvar => simp [VLevel.ofLevel] at H

/-- The original source translation supplies the initial native invariant
for replay under an additional fresh elimination universe. -/
theorem TrExprS.source_fixed_dropFresh
    (hfresh : fresh ∉ Us) (H : TrExprS env Us Δ e e') :
    Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e = e := by
  induction H with
  | sort hlevel =>
    simp [Expr.instantiateLevelParamsCore', ofLevel_fixed_dropFresh hfresh hlevel]
  | const _ hlevels _ =>
    simp only [Expr.instantiateLevelParamsCore']
    congr 1
    apply List.map_id''' _
    intro level hlevel
    obtain ⟨target, _, htarget⟩ := Lean4Lean.List.Forall₂.forall_exists_l (List.mapM_eq_some.mp hlevels) _ hlevel
    exact ofLevel_fixed_dropFresh hfresh htarget
  | bvar | fvar | lit => rfl
  | app _ _ _ _ ihFn ihArg | lam _ _ _ ihFn ihArg | forallE _ _ _ _ ihFn ihArg =>
    simp [Expr.instantiateLevelParamsCore', ihFn, ihArg]
  | letE _ _ _ _ ihTy ihVal ihBody =>
    simp [Expr.instantiateLevelParamsCore', ihTy, ihVal, ihBody]
  | mdata _ ih | proj _ _ ih => simp [Expr.instantiateLevelParamsCore', ih]
end Lean4Lean
