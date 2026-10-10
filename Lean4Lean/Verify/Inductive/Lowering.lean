import Lean4Lean.Verify.Inductive.Basic

/-! # The lowering run, as the ordinary branch sees it

`Environment.addInductive` always runs the source checks (`checkInductiveSources`) and the
nested lowering (`ElimNestedInductive.run`) before `addInductiveAfterLowering`. The ordinary
branch is the case without auxiliary families (`res.aux2nested.size = 0`); it needs only that
the lowered types are then the source types, and nonempty. These are the statements wave 2 takes
from the lowering verification; their proofs are wave 3's (`Nested/Lowering/**` of the source
branch: `checkInductiveSources_refines`, `NestedLoweringOutput.ordinary_types_eq_source`,
`NestedLoweringOutput.resultTypes_nonempty`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The source checks of `Environment.addInductive`: no metavariable or free variable in any
header or constructor type, and no reserved auxiliary name. Stated as the executable's own
verdict. -/
def SourceSyntaxChecks (env : Environment) (types : List InductiveType) : Prop :=
  checkInductiveSources env types = .ok ()

/-- Loose-bound-variable closedness of a whole source block. Lowering re-closes constructor
types over the opened parameters, which would silently repair loose bound variables, so the
source-facing statements carry this as a hypothesis. -/
def SourceBVarClosed (types : List InductiveType) : Prop :=
  ∀ type ∈ types, type.type.Closed ∧ ∀ ctor ∈ type.ctors, ctor.type.Closed

/-- The lowering run of `Environment.addInductive`. -/
abbrev loweringRun (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (lparams : List Name) : Except Exception ElimNestedInductive.Result :=
  (ElimNestedInductive.run fuel nparams types env).run'
    { lvls := lparams.map .param, newTypes := types.toArray }

/-- A lowering result has at least the source families. -/
theorem loweringRun.types_nonempty {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (h : loweringRun env fuel nparams types lparams = .ok res) : res.types ≠ [] := by
  -- WAVE 2 STUB (wave 3, Nested/Lowering): `NestedLoweringOutput.resultTypes_nonempty`.
  have := h; sorry

/-- A lowering run that introduces no auxiliary family returns the source types literally. -/
theorem loweringRun.ordinary_types_eq_source {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (hsources : SourceSyntaxChecks env types) (hclosed : SourceBVarClosed types)
    (h : loweringRun env fuel nparams types lparams = .ok res)
    (haux : res.aux2nested.size = 0) : res.types = types := by
  -- WAVE 2 STUB (wave 3, Nested/Lowering): `NestedLoweringOutput.ordinary_types_eq_source`.
  have := hsources; have := hclosed; have := h; have := haux; sorry

/-- `Environment.addInductive` is the source checks, the lowering run and
`addInductiveAfterLowering`. -/
theorem Environment.addInductive.WF (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hfinish : ∀ res, SourceSyntaxChecks env types →
      loweringRun env fuel.inductiveFuel nparams types lparams = .ok res →
      (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe allowPrimitive
        fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF Q := by
  unfold Environment.addInductive
  refine Except.WF.bind (x := checkInductiveSources env types) (Q := fun _ =>
    SourceSyntaxChecks env types) (fun u h => by cases u; exact h) fun _ hsrc => ?_
  exact Except.WF.bind (x := loweringRun env fuel.inductiveFuel nparams types lparams)
    (Q := fun res => loweringRun env fuel.inductiveFuel nparams types lparams = .ok res)
    (fun _ h => h) fun res hres => Hfinish res hsrc hres

end VerifyInductive
end Lean4Lean
