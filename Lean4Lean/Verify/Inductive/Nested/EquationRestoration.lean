import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Independent abstract counterpart of `ExprReplacement`.  A successful
node replacement stops traversal; otherwise the relation records the exact
structural recursion through `VExpr`.  The callback is specification data:
later certificates interpret its hit cases as auxiliary-family expansion,
constructor restoration, or auxiliary-recursor renaming. -/
inductive VExprRestoration (replaceNode : VExpr → Option VExpr) :
    VExpr → VExpr → Prop
  | hit (h : replaceNode input = some output) :
      VExprRestoration replaceNode input output
  | bvar (h : replaceNode (.bvar i) = none) :
      VExprRestoration replaceNode (.bvar i) (.bvar i)
  | sort (h : replaceNode (.sort u) = none) :
      VExprRestoration replaceNode (.sort u) (.sort u)
  | const (h : replaceNode (.const name levels) = none) :
      VExprRestoration replaceNode (.const name levels) (.const name levels)
  | app (h : replaceNode (.app fn arg) = none)
      (hfn : VExprRestoration replaceNode fn fn')
      (harg : VExprRestoration replaceNode arg arg') :
      VExprRestoration replaceNode (.app fn arg) (.app fn' arg')
  | lam (h : replaceNode (.lam domain body) = none)
      (hdomain : VExprRestoration replaceNode domain domain')
      (hbody : VExprRestoration replaceNode body body') :
      VExprRestoration replaceNode (.lam domain body) (.lam domain' body')
  | forallE (h : replaceNode (.forallE domain body) = none)
      (hdomain : VExprRestoration replaceNode domain domain')
      (hbody : VExprRestoration replaceNode body body') :
      VExprRestoration replaceNode (.forallE domain body)
        (.forallE domain' body')

/-- A structural abstract restoration preserves absence of the restored
recursor names whenever each atomic hit does.  This is the field-side lemma
needed by guarded iota reconstruction; recursive-call hits are handled by a
separate call-shape certificate. -/
theorem VExprRestoration.containsAnyConst_eq_false
    (H : VExprRestoration replaceNode input output)
    (Hhit : ∀ {source target}, replaceNode source = some target →
      source.containsAnyConst names = false →
      target.containsAnyConst restoredNames = false)
    (Hconst : ∀ {name levels}, replaceNode (.const name levels) = none →
      names.contains name = false → restoredNames.contains name = false)
    (hinput : input.containsAnyConst names = false) :
    output.containsAnyConst restoredNames = false := by
  induction H with
  | hit h => exact Hhit h hinput
  | bvar | sort => rfl
  | @const name levels h =>
      have hsource : names.contains name = false := by
        simpa [VExpr.containsAnyConst] using hinput
      simpa [VExpr.containsAnyConst] using Hconst h hsource
  | app h hfn harg ihfn iharg =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hinput ⊢
      exact ⟨ihfn hinput.1, iharg hinput.2⟩
  | lam h hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hinput ⊢
      exact ⟨ihdomain hinput.1, ihbody hinput.2⟩
  | forallE h hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hinput ⊢
      exact ⟨ihdomain hinput.1, ihbody hinput.2⟩

end VerifyInductive

namespace VExpr

/-- Uniform renaming of abstract constants.  Auxiliary-family replacement is
handled by `VExprRestoration`; this operation isolates the orthogonal change
of generated auxiliary recursor names. -/
def renameConsts (rename : Name → Name) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const name levels => .const (rename name) levels
  | .app fn arg => .app (fn.renameConsts rename) (arg.renameConsts rename)
  | .lam domain body =>
      .lam (domain.renameConsts rename) (body.renameConsts rename)
  | .forallE domain body =>
      .forallE (domain.renameConsts rename) (body.renameConsts rename)

@[simp] theorem renameConsts_mkApps
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).renameConsts rename =
      VExpr.mkApps (fn.renameConsts rename)
        (args.map (VExpr.renameConsts rename)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
      change
        renameConsts rename (VExpr.mkApps (.app fn arg) args) =
          VExpr.mkApps
            (.app (renameConsts rename fn) (renameConsts rename arg))
            (args.map (renameConsts rename))
      simpa [renameConsts] using ih (.app fn arg)

@[simp] theorem getAppFnArgs_renameConsts (e : VExpr) :
    (e.renameConsts rename).getAppFnArgs =
      let (fn, args) := e.getAppFnArgs
      (fn.renameConsts rename, args.map (VExpr.renameConsts rename)) := by
  induction e with
  | app fn arg ihFn _ =>
      simp only [VExpr.renameConsts, VExpr.getAppFnArgs_app, ihFn]
      simp
  | bvar | sort | const | lam | forallE => rfl

theorem IsFieldApp.renameConsts
    (H : IsFieldApp fieldVars depth e) :
    IsFieldApp fieldVars depth (e.renameConsts rename) := by
  rcases H with ⟨field, hfield, args, hargs⟩
  refine ⟨field, hfield, args.map (VExpr.renameConsts rename), ?_⟩
  rw [VExpr.getAppFnArgs_renameConsts, hargs]
  rfl

/-- Injective recursor renaming preserves the independent guarded-iota
judgment.  This is separate from equation restoration: the later hit
interpreter only has to identify its auxiliary recursor renaming function and
prove injectivity. -/
theorem GuardedIota.renameConsts
    (H : GuardedIota recursors fieldVars depth e)
    (hinjective : Function.Injective rename) :
    GuardedIota (recursors.map rename) fieldVars depth
      (e.renameConsts rename) := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | @const name depth levels hname =>
      apply VExpr.GuardedIota.const
      intro hmem
      rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
      exact hname (hinjective heq ▸ hsource)
  | app hfn harg ihfn iharg => exact .app ihfn iharg
  | lam hdomain hbody ihdomain ihbody => exact .lam ihdomain ihbody
  | forallE hdomain hbody ihdomain ihbody =>
      exact .forallE ihdomain ihbody
  | @recCall recursor init major depth levels hrecursor hargs hmajor ihargs =>
      rw [VExpr.renameConsts_mkApps]
      simp only [List.map_append, List.map_cons, List.map_nil]
      apply VExpr.GuardedIota.recCall
      · exact List.mem_map.mpr ⟨recursor, hrecursor, rfl⟩
      · intro arg harg
        have harg' : arg ∈
            (init ++ [major]).map (VExpr.renameConsts rename) := by
          simpa [List.map_append] using harg
        rcases List.mem_map.mp harg' with ⟨source, hsource, rfl⟩
        exact ihargs source hsource
      · exact hmajor.renameConsts

end VExpr

namespace VerifyInductive

/-- Pointwise restoration of a list of constructor fields preserves their
order and length. -/
abbrev VExprRestorationList (replaceNode : VExpr → Option VExpr) :=
  List.Forall₂ (VExprRestoration replaceNode)

theorem VExprRestorationList.length_eq
    (H : VExprRestorationList replaceNode sources targets) :
    sources.length = targets.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end VerifyInductive
end Lean4Lean
