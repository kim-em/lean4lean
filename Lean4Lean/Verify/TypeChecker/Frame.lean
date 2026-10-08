import Lean4Lean.Verify.TypeChecker.FrameDefEq

/-!
# Frame lemma for the core checker

Every function of the executable core checker is framed (`FrameDefs.lean`): a successful run in a
local context extended by ghost declarations is the identical run in the context without them,
with ghost-free result and final state. The `Inner` functions are proved framed for framed
methods in `FrameInfer.lean`, `FrameWHNF.lean` and `FrameDefEq.lean` (on the combinators of
`FrameBasic.lean` and the expression lemmas of `FrameExpr.lean`); here the fuel fixpoint
`Methods.withFuel` is framed by induction on the fuel, and the public `M` entry points follow.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

theorem Methods.withFuel_framed (G : FVarId → Prop) : ∀ n, (Methods.withFuel n).Framed G
  | 0 => {
      isDefEqCore := fun _ _ _ _ => .throw
      whnfCore := fun _ _ _ => .throw
      whnf := fun _ _ => .throw
      inferType := fun _ _ _ => .throw }
  | n + 1 =>
    have ih := Methods.withFuel_framed G n
    { isDefEqCore := fun _ _ ht hs => Inner.isDefEqCore'.framed ht hs ih
      whnfCore := fun _ cheapProj he => Inner.whnfCore'.framed cheapProj he ih
      whnf := fun _ he => Inner.whnf'.framed he ih
      inferType := fun _ inferOnly he => Inner.inferType'.framed inferOnly he ih }

/-- Running a framed `RecM` computation with the configured fuel is framed. -/
theorem RecM.Framed.run {x : RecM α} {R} (h : RecM.Framed G x R) : M.Framed G x.run R := by
  unfold RecM.run
  exact M.Framed.read (fun _ _ hr => by simp only [hr.ctx_eq.2.2.2.2]) fun _ _ _ =>
    h (Methods.withFuel_framed G _)

theorem inferType_framed (G : FVarId → Prop) (e : Expr) (inferOnly : Bool) (h : GF G e) :
    M.Framed G (TypeChecker.inferType e inferOnly) (GF G) :=
  (RecM.Framed.inferType h).run

theorem checkType_framed (G : FVarId → Prop) (e : Expr) (h : GF G e) :
    M.Framed G (TypeChecker.checkType e) (GF G) :=
  inferType_framed G e false h

theorem whnf_framed (G : FVarId → Prop) (e : Expr) (h : GF G e) :
    M.Framed G (TypeChecker.whnf e) (GF G) :=
  (RecM.Framed.whnf h).run

theorem whnfCore_framed (G : FVarId → Prop) (e : Expr) (h : GF G e) :
    M.Framed G (TypeChecker.whnfCore e) (GF G) :=
  (RecM.Framed.whnfCore h).run

theorem isDefEq_framed (G : FVarId → Prop) (t s : Expr) (ht : GF G t) (hs : GF G s) :
    M.Framed G (TypeChecker.isDefEq t s) fun _ => True :=
  (RecM.Framed.isDefEq ht hs).run

theorem isProp_framed (G : FVarId → Prop) (e : Expr) (h : GF G e) :
    M.Framed G (TypeChecker.isProp e) fun _ => True :=
  (Inner.isProp.framed h).run

theorem ensureSort_framed (G : FVarId → Prop) (t s : Expr) (h : GF G t) :
    M.Framed G (TypeChecker.ensureSort t s) (GF G) :=
  (Inner.ensureSortCore.framed h).run

theorem ensureForall_framed (G : FVarId → Prop) (t s : Expr) (h : GF G t) :
    M.Framed G (TypeChecker.ensureForall t s) (GF G) :=
  (Inner.ensureForallCore.framed h).run

theorem ensureType_framed (G : FVarId → Prop) (e : Expr) (inferOnly : Bool) (h : GF G e) :
    M.Framed G (TypeChecker.ensureType e inferOnly) (GF G) :=
  (inferType_framed G e inferOnly h).bind fun _ h => ensureSort_framed G _ e h

theorem unfoldDefinition_framed (G : FVarId → Prop) (e : Expr) (h : GF G e) :
    M.Framed G (TypeChecker.unfoldDefinition e) (GF G) :=
  (Inner.unfoldDefinition.framed h).run.bind fun o ho => .pure (by
    cases o with
    | none => exact h
    | some x => exact ho rfl)

end Lean4Lean.TypeChecker
