import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMinorFields

/-! Lambda-only contexts and their closing telescopes.

The generic up-set restriction of a translated context that used to live here
relied on translation strengthening (`TrExprS.weakFV'_inv`), which is not
valid in general; it had no remaining users and was removed.  Narrow contexts
are produced directly by the checker context of `AddInductive` instead (see
`docs/inductives/STRENGTHENING.md`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

/-- A context of lambda declarations pairs with its own free-variable list. -/
theorem VLCtx.allLams_forall₂ : ∀ (Δ : VLCtx),
    (∀ entry ∈ Δ, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty)) →
    List.Forall₂ (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type)) Δ.fvars Δ
  | [], _ => .nil
  | entry :: Δ, h => by
    obtain ⟨fv, deps, ty, rfl⟩ := h entry (List.mem_cons_self ..)
    exact .cons ⟨deps, ty, rfl⟩ (allLams_forall₂ Δ fun e he => h e (List.mem_cons_of_mem _ he))

/-- Close every declaration of a lambda-only context into abstract binders. -/
theorem TrExprS.closeAllLams {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (hlams : ∀ entry ∈ Δ, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty))
    (hnodup : Δ.fvars.Nodup) (Htr : TrExprS env Us Δ e e') :
    TrExprS env Us (VerifyInductive.abstractForallContext Δ.toCtx.reverse [])
      (e.abstractList Δ.fvars.reverse) e' := by
  have h := VerifyInductive.TrExprS.abstractFVarLambdaSuffix (domains := [])
    (VLCtx.allLams_forall₂ Δ hlams) hnodup
    (by simpa [VerifyInductive.abstractForallContext] using Htr)
  simpa using h


end Lean4Lean
