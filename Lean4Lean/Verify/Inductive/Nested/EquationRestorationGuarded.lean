import Lean4Lean.Verify.Inductive.Nested.EquationRestorationNodeSemantics

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Structural restoration of a guarded equation fragment. Atomic
family/constructor replacements are justified by recursor-freeness;
recursor applications are represented as applications on both sides with
their major-field provenance retained. -/
inductive GuardedExprRestoration
      (replaceNode : VExpr → Option VExpr)
      (sourceRecursors targetRecursors : List Name)
      (fieldVars : List Nat) : Nat → VExpr → VExpr → Prop
    | hit (hhit : replaceNode source = some target)
        (hsource : source.GuardedIota sourceRecursors fieldVars depth)
        (htargetFree : target.containsAnyConst targetRecursors = false) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth source target
    | bvar (hnone : replaceNode (.bvar index) = none) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.bvar index) (.bvar index)
    | sort (hnone : replaceNode (.sort level) = none) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.sort level) (.sort level)
    | const (hnone : replaceNode (.const name levels) = none)
        (hsource : name ∉ sourceRecursors)
        (htarget : name ∉ targetRecursors) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.const name levels) (.const name levels)
    | app (hnone : replaceNode (.app fn arg) = none)
        (hfn : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth fn fn')
        (harg : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth arg arg') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.app fn arg) (.app fn' arg')
    | lam (hnone : replaceNode (.lam domain body) = none)
        (hdomain : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth domain domain')
        (hbody : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars (depth + 1) body body') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.lam domain body) (.lam domain' body')
    | forallE (hnone : replaceNode (.forallE domain body) = none)
        (hdomain : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth domain domain')
        (hbody : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars (depth + 1) body body') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.forallE domain body) (.forallE domain' body')
    | recCall
        (sourceRecursor targetRecursor : Name)
        (sourceLevels targetLevels : List VLevel)
        (sourceInit targetInit : List VExpr)
        (sourceMajor targetMajor : VExpr)
        (hsourceMem : sourceRecursor ∈ sourceRecursors)
        (htargetMem : targetRecursor ∈ targetRecursors)
        (hsourceMajor : sourceMajor.IsFieldApp fieldVars depth)
        (htargetMajor : targetMajor.IsFieldApp fieldVars depth)
        (hrestoration : VExprRestoration replaceNode
          (VExpr.mkApps (.const sourceRecursor sourceLevels)
            (sourceInit ++ [sourceMajor]))
          (VExpr.mkApps (.const targetRecursor targetLevels)
            (targetInit ++ [targetMajor])))
        (htargetArgs : ∀ target ∈ targetInit ++ [targetMajor],
          target.GuardedIota targetRecursors fieldVars depth) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth
          (VExpr.mkApps (.const sourceRecursor sourceLevels)
            (sourceInit ++ [sourceMajor]))
          (VExpr.mkApps (.const targetRecursor targetLevels)
            (targetInit ++ [targetMajor]))

/-- Structural guarded restoration entails guardedness of the target. -/
theorem GuardedExprRestoration.targetGuarded
    (H : GuardedExprRestoration replaceNode sourceRecursors targetRecursors
      fieldVars depth source target) :
    target.GuardedIota targetRecursors fieldVars depth := by
  induction H with
  | hit _ _ hfree =>
      exact VExpr.GuardedIota.ofContainsAnyConstFalse hfree
  | bvar => exact .bvar
  | sort => exact .sort
  | const _ _ htarget => exact .const htarget
  | app _ _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ _ ihdomain ihbody => exact .lam ihdomain ihbody
  | forallE _ _ _ ihdomain ihbody => exact .forallE ihdomain ihbody
  | recCall _ _ _ _ _ _ _ _ _ htargetMem _ htargetMajor _ htargetArgs =>
      exact .recCall htargetMem htargetArgs htargetMajor

end VerifyInductive
end Lean4Lean
