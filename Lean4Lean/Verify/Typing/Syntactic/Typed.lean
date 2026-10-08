import Lean4Lean.Verify.Typing.Syntactic.Transport

/-!
# Typed translation as syntactic translation plus typing

`TrExprS` carries a typing premise at `app`, `lam`, `forallE`, `letE`, `lit`, `proj` and
`const`. Over an ordered environment and a well-formed context, all of them except two are
consequences of the typing of the *result* of the translation, by inversion
(`HasType.app_inv`, `HasType.lam_inv`, `HasType.forallE_inv`, `HasType.proj_inv`,
`HasType.const_inv`). The two exceptions are about source syntax that the translation erases:

* a let-bound value is inlined, so the typing of the value at the declared type
  (`TrExprS.letE`) is not visible in the result when the variable is unused;
* a literal is translated to its constructor encoding, and the presence of the literal's
  primitive types (`TrExprS.lit`, `VEnv.ContainsLits`) is not visible in the result: the
  encoding of `""` mentions neither `Char.ofNat` nor `Nat`.

`TrResidual` collects exactly these two obligations, and

  `TrExprS env Us Δ e e' ↔ TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' ∧ TrResidual env Us Δ e`

(`TrExprS.iff_typed`). `TrTyped` is the right-hand side. The residual is trivial on let-free
syntax without literals (`TrResidual.of_simple`).
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

variable (env : VEnv) (Us : List Name) in
/-- The typing obligations of `TrExprS` that the typing of the translated term does not
witness: let-bound values are typed at their declared types, and literals have their primitive
types present. Binders record the syntactic translation of their domain, to know the context of
the body. -/
inductive TrResidual : VLCtx → Expr → Prop
  | bvar : TrResidual Δ (.bvar i)
  | fvar : TrResidual Δ (.fvar fv)
  | sort : TrResidual Δ (.sort u)
  | const : TrResidual Δ (.const c us)
  | app : TrResidual Δ f → TrResidual Δ a → TrResidual Δ (.app f a)
  | lam : TrSyn Us Δ ty ty' → TrResidual Δ ty → TrResidual ((none, .vlam ty') :: Δ) body →
    TrResidual Δ (.lam name ty body bi)
  | forallE : TrSyn Us Δ ty ty' → TrResidual Δ ty → TrResidual ((none, .vlam ty') :: Δ) body →
    TrResidual Δ (.forallE name ty body bi)
  | letE : TrSyn Us Δ ty ty' → TrSyn Us Δ val val' →
    env.HasType Us.length Δ.toCtx val' ty' →
    TrResidual Δ ty → TrResidual Δ val → TrResidual ((none, .vlet ty' val') :: Δ) body →
    TrResidual Δ (.letE name ty val body nd)
  | lit : env.ContainsLits l → TrResidual Δ l.toConstructor → TrResidual Δ (.lit l)
  | mdata : TrResidual Δ e → TrResidual Δ (.mdata d e)
  | proj : TrResidual Δ e → TrResidual Δ (.proj s i e)

/-- Typed translation: a syntactic translation whose result is well typed, with the residual
obligations on erased syntax. Equivalent to `TrExprS` (`TrExprS.iff_typed`). -/
def TrTyped (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' ∧ TrResidual env Us Δ e

/-! ### From `TrExprS` -/

theorem TrExprS.residual (H : TrExprS env Us Δ e e') : TrResidual env Us Δ e := by
  induction H with
  | bvar | fvar | sort | const => constructor
  | app _ _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ h1 _ _ ih2 => exact .lam h1.toTrSyn (by assumption) ih2
  | forallE _ _ h1 _ _ ih2 => exact .forallE h1.toTrSyn (by assumption) ih2
  | letE h0 h1 h2 _ ih1 ih2 ih3 => exact .letE h1.toTrSyn h2.toTrSyn h0 ih1 ih2 ih3
  | lit h _ ih => exact .lit h ih
  | mdata _ ih => exact .mdata ih
  | proj _ _ ih => exact .proj ih

/-! ### To `TrExprS` -/

/-- A syntactic translation with a well-typed result and the residual obligations is a typed
translation. The typing premises of `TrExprS` at applications, binders, projections and
constants are recovered by inversion from the typing of the result. -/
theorem TrSyn.toTrExprS (henv : env.Ordered) (H : TrSyn Us Δ e e')
    (hΔ : Δ.WF env Us.length) (hwf : VExpr.WF env Us.length Δ.toCtx e')
    (hr : TrResidual env Us Δ e) : TrExprS env Us Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h =>
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΔ.toCtx
    exact .const hci h ((List.mapM_eq_some.1 h).length_eq.trans hlen)
  | app _ _ ih1 ih2 =>
    let .app r1 r2 := hr
    obtain ⟨A, B, h1, h2⟩ := hwf.app_inv henv hΔ.toCtx
    exact .app h1 h2 (ih1 hΔ ⟨_, h1⟩ r1) (ih2 hΔ ⟨_, h2⟩ r2)
  | lam s1 _ ih1 ih2 =>
    let .lam s1' r1 r2 := hr
    cases s1.unique s1'
    obtain ⟨hty, hbody⟩ := hwf.lam_inv henv hΔ.toCtx
    have ⟨_, hty'⟩ := hty
    exact .lam hty (ih1 hΔ ⟨_, hty'⟩ r1) (ih2 ⟨hΔ, nofun, hty⟩ hbody r2)
  | forallE s1 _ ih1 ih2 =>
    let .forallE s1' r1 r2 := hr
    cases s1.unique s1'
    obtain ⟨_, hT⟩ := hwf
    obtain ⟨hty, hbody⟩ := HasType.forallE_inv henv hT
    have ⟨_, hty'⟩ := hty
    have ⟨_, hbody'⟩ := hbody
    exact .forallE hty hbody (ih1 hΔ ⟨_, hty'⟩ r1) (ih2 ⟨hΔ, nofun, hty⟩ ⟨_, hbody'⟩ r2)
  | letE s1 s2 _ ih1 ih2 ih3 =>
    let .letE s1' s2' hv r1 r2 r3 := hr
    cases s1.unique s1'; cases s2.unique s2'
    obtain ⟨_, hty⟩ := IsDefEq.isType henv hΔ.toCtx hv
    exact .letE hv (ih1 hΔ ⟨_, hty⟩ r1) (ih2 hΔ ⟨_, hv⟩ r2) (ih3 ⟨hΔ, nofun, hv⟩ hwf r3)
  | lit _ ih =>
    let .lit hl r := hr
    exact .lit hl (ih hΔ hwf r)
  | mdata _ ih =>
    let .mdata r := hr
    exact .mdata (ih hΔ hwf r)
  | proj _ ih =>
    let .proj r := hr
    obtain ⟨_, hT⟩ := hwf
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      HasType.proj_inv henv hΔ.toCtx hT
    exact .proj (ih hΔ ⟨_, hmajor.hasType.2⟩ r) ⟨_, hT⟩

/-- **The decomposition of typed translation.** Over an ordered environment and a well-formed
context, a typed translation is exactly a syntactic translation whose result is well typed and
whose erased syntax meets the residual obligations. -/
theorem TrExprS.iff_typed (henv : env.Ordered) (hΔ : Δ.WF env Us.length) :
    TrExprS env Us Δ e e' ↔ TrTyped env Us Δ e e' :=
  ⟨fun H => ⟨H.toTrSyn, H.wf henv hΔ, H.residual⟩,
   fun ⟨H, hwf, hr⟩ => H.toTrExprS henv hΔ hwf hr⟩

/-! ### The residual on simple syntax -/

/-- Let-free syntax without literals: the residual obligations are vacuous on it. -/
def Expr.LetLitFree : Expr → Prop
  | .bvar _ | .fvar _ | .sort _ | .const .. | .mvar _ => True
  | .lit _ | .letE .. => False
  | .app f a | .lam _ f a _ | .forallE _ f a _ => LetLitFree f ∧ LetLitFree a
  | .mdata _ e | .proj _ _ e => LetLitFree e

theorem TrResidual.of_simple : ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr},
    Expr.LetLitFree e → TrSyn Us Δ e e' → TrResidual env Us Δ e
  | _, .bvar _, _, _, _ => .bvar
  | _, .fvar _, _, _, _ => .fvar
  | _, .sort _, _, _, _ => .sort
  | _, .const .., _, _, _ => .const
  | _, .app .., _, h, .app s1 s2 => .app (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .lam .., _, h, .lam s1 s2 => .lam s1 (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .forallE .., _, h, .forallE s1 s2 => .forallE s1 (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .mdata .., _, h, .mdata s => .mdata (of_simple h s)
  | _, .proj .., _, h, .proj s => .proj (of_simple h s)

/-- On let-free syntax without literals, a typed translation is a syntactic translation with a
well-typed result. -/
theorem TrExprS.iff_syn_wf (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (hs : Expr.LetLitFree e) :
    TrExprS env Us Δ e e' ↔ TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' :=
  ⟨fun H => ⟨H.toTrSyn, H.wf henv hΔ⟩,
   fun ⟨H, hwf⟩ => H.toTrExprS henv hΔ hwf (.of_simple hs H)⟩

/-! ### Transport of the typed layer

A typed lemma is the syntactic lemma, the typing lemma for the result, and the transport of the
residual, which only moves the typing of let-bound values. Bound-variable weakening as the
example: compare `TrExprS.weakBV`, which re-proves the syntax in every case. -/

theorem TrResidual.weakBV (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrResidual env Us Δ e) : TrResidual env Us Δ' (e.liftLooseBVars' dk dn) := by
  induction H generalizing Δ' dk k with
  | bvar | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam s _ _ ih1 ih2 => exact .lam (s.weakBV W) (ih1 W) (ih2 (W.cons _))
  | forallE s _ _ ih1 ih2 => exact .forallE (s.weakBV W) (ih1 W) (ih2 (W.cons _))
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (s1.weakBV W) (s2.weakBV W) (hv.weakN henv W.toCtx) (ih1 W) (ih2 W)
      (ih3 (W.cons _))
  | lit hl _ ih =>
    refine .lit hl (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrTyped.weakBV (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrTyped env Us Δ e e') :
    TrTyped env Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) :=
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s.weakBV W, ⟨_, h.weakN henv W.toCtx⟩, r.weakBV henv W⟩

end Lean4Lean
