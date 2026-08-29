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
      (replaceNode : VExpr → VExpr → Prop)
      (sourceRecursors targetRecursors : List Name)
      (fieldVars : List Nat) : Nat → VExpr → VExpr → Prop
    | hit (hhit : replaceNode source target)
        (hsource : source.GuardedIota sourceRecursors fieldVars depth)
        (htargetGuarded : target.GuardedIota targetRecursors fieldVars depth) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth source target
    | leaf
        (htarget : source.GuardedIota targetRecursors fieldVars depth) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth source source
    | bvar :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.bvar index) (.bvar index)
    | sort :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.sort level) (.sort level)
    | const (hsource : name ∉ sourceRecursors)
        (htarget : name ∉ targetRecursors) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.const name levels) (.const name levels)
    | app (hfn : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth fn fn')
        (harg : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth arg arg') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.app fn arg) (.app fn' arg')
    | lam (hdomain : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth domain domain')
        (hbody : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars (depth + 1) body body') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.lam domain body) (.lam domain' body')
    | forallE (hdomain : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth domain domain')
        (hbody : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars (depth + 1) body body') :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth (.forallE domain body) (.forallE domain' body')
    | projection
        (sourceExpansion : VExpr.ProjectionSupportExpansion
          sourceMajor sourceTarget)
        (targetExpansion : VExpr.ProjectionSupportExpansion
          targetMajor targetTarget)
        (hmajor : GuardedExprRestoration replaceNode sourceRecursors
          targetRecursors fieldVars depth sourceMajor targetMajor) :
        GuardedExprRestoration replaceNode sourceRecursors targetRecursors
          fieldVars depth sourceTarget targetTarget
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
  | hit _ _ hguarded => exact hguarded
  | leaf htarget => exact htarget
  | bvar => exact .bvar
  | sort => exact .sort
  | const _ htarget => exact .const htarget
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihdomain ihbody => exact .lam ihdomain ihbody
  | forallE _ _ ihdomain ihbody => exact .forallE ihdomain ihbody
  | projection _ targetExpansion _ ihmajor =>
      exact .projection targetExpansion ihmajor
  | recCall _ _ _ _ _ _ _ _ _ htargetMem _ htargetMajor _ htargetArgs =>
      exact .recCall htargetMem htargetArgs htargetMajor

end VerifyInductive
end Lean4Lean
