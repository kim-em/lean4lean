import Lean4Lean.Verify.Typing.Syntactic.Typed
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The strengthening boundary

With translation split into syntax and typing, strengthening splits the same way:

* restricting the *syntax* of a translation is elementary: a source that does not use some
  binders or free variables translates without them, and its translation in the larger context
  is the lift (`TrSyn.lowerBV`, `TrSyn.restrictFV`);
* restricting the *typing* is not (section 5.1 of `docs/inductives/DESIGN.md`): what remains of a
  typed translation in the smaller context is exactly the typing of the restricted result and the
  residual of the restricted source (`TrExprS.lowerBV_iff`).

The projection walk's certificate (`TelTrN`, `Verify/Typing/TelescopeTranslation.lean`) is built
the same way: a syntactic translation together with the typing-only certificate `TelWF`, which
records the typing of each residual telescope in its smaller context.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

/-- **The strengthening boundary.** A typed translation of a source that does not use some
bound variables is the lift of a syntactic translation in the smaller context, for free; it is a
typed translation there exactly when its result is well typed there and the source's residual
obligations hold there. Neither of the latter follows from the larger context in general. -/
theorem TrExprS.lowerBV_iff (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hΔ : Δ.WF env Us.length) (H : TrExprS env Us Δ' (Expr.liftLooseBVars' e₀ dk dn) e') :
    ∃ e₀', e' = e₀'.liftN n k ∧ TrSyn Us Δ e₀ e₀' ∧
      (TrExprS env Us Δ e₀ e₀' ↔
        VExpr.WF env Us.length Δ.toCtx e₀' ∧ TrResidual env Us Δ e₀) := by
  obtain ⟨e₀', s, rfl⟩ := H.toTrSyn.lowerBV W
  exact ⟨e₀', rfl, s, fun h => ⟨h.wf henv hΔ, h.residual⟩, fun ⟨h1, h2⟩ => s.toTrExprS henv hΔ h1 h2⟩

/-- The same for free variables: no typing is involved in the syntactic part. -/
theorem TrExprS.restrictFV_iff (henv : env.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k)
    (hΔ' : Δ'.WF env Us.length) (hΔ : Δ.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀', e' = e₀'.liftN n k ∧ TrSyn Us Δ e e₀' ∧
      (TrExprS env Us Δ e e₀' ↔
        VExpr.WF env Us.length Δ.toCtx e₀' ∧ TrResidual env Us Δ e) := by
  obtain ⟨e₀', s, rfl⟩ := H.toTrSyn.restrictFV W hΔ'.fvars_nodup hfv
  exact ⟨e₀', rfl, s, fun h => ⟨h.wf henv hΔ, h.residual⟩, fun ⟨h1, h2⟩ => s.toTrExprS henv hΔ h1 h2⟩

end Lean4Lean
