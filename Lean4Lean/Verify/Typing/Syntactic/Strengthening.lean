import Lean4Lean.Verify.Typing.Syntactic.Typed
import Lean4Lean.Verify.Typing.TelescopeTranslationLemmas

/-!
# The strengthening boundary, and constructor telescopes

With translation split into syntax and typing, strengthening splits the same way:

* restricting the *syntax* of a translation is elementary: a source that does not use some
  binders or free variables translates without them, and its translation in the larger context
  is the lift (`TrSyn.lowerBV`, `TrSyn.restrictFV`);
* restricting the *typing* is not (section 5.1 of `docs/inductives/DESIGN.md`): what remains of a
  typed translation in the smaller context is exactly the typing of the restricted result and the
  residual of the restricted source (`TrExprS.lowerBV_iff`).

The projection walk's certificate `TelTrN` is then a syntactic translation together with a
typing-only certificate `TelWF` (`TelTrN.iff_syn_telWF`): the existence of the lowered
translation at a deleted binder, which `TelTrN` records as a premise, is a theorem, and what the
certificate genuinely carries is the typing of the residual telescope in the smaller context.
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

/-! ### Constructor telescopes -/

variable (env : VEnv) (Us : List Name) in
/-- The typing content of a depth-bounded telescope certificate: the typing of the translated
telescope and of every residual telescope obtained by deleting unused binders, each in its own
context, with the residual obligations of the source. The syntactic content of `TelTrN` (that
the deleted telescopes translate, to the lowered terms) is not part of it: it is
`TrSyn.lower`. -/
inductive TelWF : Nat → VLCtx → Expr → VExpr → Prop
  | zero {Δ : VLCtx} {e : Expr} {e' : VExpr} :
    VExpr.WF env Us.length Δ.toCtx e' → TrResidual env Us Δ e → TelWF 0 Δ e e'
  | succ {k : Nat} {Δ : VLCtx} {n d b bi d' b'} :
    VExpr.WF env Us.length Δ.toCtx (.forallE d' b') →
    TrResidual env Us Δ (.forallE n d b bi) →
    TelWF k ((none, .vlam d') :: Δ) b b' →
    (∀ b₀ b₀', b = Expr.liftLooseBVars' b₀ 0 1 → b' = VExpr.lift b₀' → TelWF k Δ b₀ b₀') →
    TelWF (k + 1) Δ (.forallE n d b bi) (.forallE d' b')

theorem TelTrN.toTelWF (henv : env.Ordered) (H : TelTrN env Us n Δ e e')
    (hΔ : Δ.WF env Us.length) : TelWF env Us n Δ e e' := by
  induction H with
  | zero h => exact .zero (h.wf henv hΔ) h.residual
  | succ h1 _ _ _ ih2 ih4 =>
    let .forallE hd _ _ _ := h1
    exact .succ (h1.wf henv hΔ) h1.residual (ih2 ⟨hΔ, nofun, hd⟩)
      fun b₀ b₀' hb hb' => ih4 b₀ b₀' hb hb' hΔ

/-- **`TelTrN` is syntax plus typing.** The bounded certificate is a syntactic translation
together with the typing-only certificate `TelWF`. -/
theorem TelTrN.of_syn_telWF (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (S : TrSyn Us Δ e e') (H : TelWF env Us n Δ e e') : TelTrN env Us n Δ e e' := by
  induction H with
  | zero hwf hr => exact .zero (S.toTrExprS henv hΔ hwf hr)
  | @succ k Δ nm d b bi d' b' hwf hr _ _ ih3 ih4 =>
    have hTop := S.toTrExprS henv hΔ hwf hr
    let .forallE hd _ _ _ := hTop
    let .forallE _ sb := S
    refine .succ hTop (ih3 ⟨hΔ, nofun, hd⟩ sb) ?_ ?_
    · intro b₀ hb
      subst hb
      obtain ⟨b₀', _, rfl⟩ := sb.lower
      exact ⟨b₀', rfl⟩
    · intro b₀ b₀' hb hb'
      subst hb
      obtain ⟨x, sx, hx⟩ := sb.lower
      have : x = b₀' := VExpr.liftN_inj.1 (hx.symm.trans hb')
      subst this
      exact ih4 _ _ rfl hb' hΔ sx

theorem TelTrN.iff_syn_telWF (henv : env.Ordered) (hΔ : Δ.WF env Us.length) :
    TelTrN env Us n Δ e e' ↔ TrSyn Us Δ e e' ∧ TelWF env Us n Δ e e' :=
  ⟨fun H => ⟨H.toTrExprS.toTrSyn, H.toTelWF henv hΔ⟩, fun ⟨S, H⟩ => .of_syn_telWF henv hΔ S H⟩

end Lean4Lean
