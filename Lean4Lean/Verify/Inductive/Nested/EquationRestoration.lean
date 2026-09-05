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
inductive VExprRestoration (replaceNode : VExpr → VExpr → Prop) :
    VExpr → VExpr → Prop
  | hit (h : replaceNode input output) :
      VExprRestoration replaceNode input output
  | leaf : VExprRestoration replaceNode input input
  | bvar :
      VExprRestoration replaceNode (.bvar i) (.bvar i)
  | sort :
      VExprRestoration replaceNode (.sort u) (.sort u)
  | const :
      VExprRestoration replaceNode (.const name levels) (.const name levels)
  | app (hfn : VExprRestoration replaceNode fn fn')
      (harg : VExprRestoration replaceNode arg arg') :
      VExprRestoration replaceNode (.app fn arg) (.app fn' arg')
  | proj (hmajor : VExprRestoration replaceNode major major') :
      VExprRestoration replaceNode (.proj typeName index major)
        (.proj typeName index major')
  | lam (hdomain : VExprRestoration replaceNode domain domain')
      (hbody : VExprRestoration replaceNode body body') :
      VExprRestoration replaceNode (.lam domain body) (.lam domain' body')
  | forallE (hdomain : VExprRestoration replaceNode domain domain')
      (hbody : VExprRestoration replaceNode body body') :
      VExprRestoration replaceNode (.forallE domain body)
        (.forallE domain' body')

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
  | .proj typeName index major =>
      .proj (rename typeName) index (major.renameConsts rename)
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
  | bvar | sort | const | proj | lam | forallE => rfl

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
  | proj hmajor ihMajor => exact .proj ihMajor
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
abbrev VExprRestorationList (replaceNode : VExpr → VExpr → Prop) :=
  List.Forall₂ (VExprRestoration replaceNode)

theorem VExprRestorationList.leaf
    (expressions : List VExpr) :
    VExprRestorationList replaceNode expressions expressions := by
  induction expressions with
  | nil => exact .nil
  | cons expression expressions ih => exact .cons .leaf ih

theorem VExprRestorationList.length_eq
    (H : VExprRestorationList replaceNode sources targets) :
    sources.length = targets.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end VerifyInductive
end Lean4Lean
