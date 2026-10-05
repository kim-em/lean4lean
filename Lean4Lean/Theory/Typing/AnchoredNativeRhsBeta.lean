import Lean4Lean.Theory.Typing.AnchoredHeadBeta
import Lean4Lean.Theory.Typing.NativeTelescope

/-! Literal formal-variable beta traces for the native RHS telescope.
The raw typed trace is constructed at the terminal body's natural type. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive FormalHeadBeta (source : List VExpr) : VExpr → VExpr → Prop where
  | beta (lookup : Lookup source index A) :
      FormalHeadBeta source (.app (.lam A body) (.bvar index)) (body.inst (.bvar index))
  | app (head : FormalHeadBeta source f g) :
      FormalHeadBeta source (.app f argument) (.app g argument)

theorem FormalHeadBeta.head (step : FormalHeadBeta source left right) : HeadBeta left right := by
  induction step with
  | beta => exact HeadBeta.contract (trailing := [])
  | app _ ih => exact ih.app _

theorem FormalHeadBeta.weak (step : FormalHeadBeta source left right)
    (W : Ctx.Lift' ρ source target) :
    FormalHeadBeta target (left.lift' ρ) (right.lift' ρ) := by
  induction step with
  | @beta index A body lookup =>
    simpa only [lift', lift'_inst_hi] using FormalHeadBeta.beta
      (body := body.lift' ρ.cons) (lookup.weak' W)
  | app _ ih => exact ih.app

theorem FormalHeadBeta.open (step : FormalHeadBeta source left right) (domains : List VExpr) :
    FormalHeadBeta (domains.reverse ++ source)
      (nativeEtaBody domains.length left) (nativeEtaBody domains.length right) := by
  induction domains generalizing source left right with
  | nil => exact step
  | cons A domains ih =>
    have one := (step.weak (Ctx.Lift'.skip (A := A) Ctx.Lift'.refl)).app (argument := .bvar 0)
    simpa only [List.length_cons, nativeEtaBody, List.reverse_cons,
      List.append_assoc, List.singleton_append, lift_eq_lift'] using ih one

inductive FormalBetaTrace (source : List VExpr) : VExpr → VExpr → Prop where
  | refl : FormalBetaTrace source expression expression
  | next : FormalHeadBeta source first middle → FormalBetaTrace source middle last →
      FormalBetaTrace source first last

theorem FormalBetaTrace.trans (first : FormalBetaTrace source a b)
    (second : FormalBetaTrace source b c) : FormalBetaTrace source a c := by
  induction first with
  | refl => exact second
  | next head _ ih => exact .next head (ih second)

theorem FormalBetaTrace.open (trace : FormalBetaTrace source left right) (domains : List VExpr) :
    FormalBetaTrace (domains.reverse ++ source)
      (nativeEtaBody domains.length left) (nativeEtaBody domains.length right) := by
  induction trace with
  | refl => exact .refl
  | next head _ ih => exact .next (head.open domains) ih

/-- The trace is independent of semantic guards and of any chosen proof
witness. Every added argument is a lookup in the literal equation telescope. -/
theorem FormalBetaTrace.nativeRhs (domains : List VExpr) (body : VExpr) (source : List VExpr) :
    FormalBetaTrace (domains.reverse ++ source)
      (nativeEtaBody domains.length (wrapLams domains body)) body := by
  induction domains generalizing source with
  | nil => exact .refl
  | cons A domains ih =>
    have first : FormalHeadBeta (A :: source)
        (.app (VExpr.lam A (wrapLams domains body)).lift (.bvar 0))
        (wrapLams domains body) := by
      simpa only [lift, liftN, instN_bvar0] using
        (FormalHeadBeta.beta (body := (wrapLams domains body).liftN 1 1)
          (Lookup.zero (Γ := source) (ty := A)))
    have opened := first.open domains
    have rest := ih (A :: source)
    simpa only [List.length_cons, nativeEtaBody, wrapLams, List.foldr_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append] using
      FormalBetaTrace.next opened rest

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Each computational edge retains equality at the one actual assigned
result type. This is a finite trace, not subject reduction inferred from an
arbitrary application typing. -/
inductive TypedBetaTrace (env : VEnv) (U : Nat) (Γ : List VExpr) (type : VExpr) :
    VExpr → VExpr → Prop where
  | refl (typed : env.HasType U Γ expression type) : TypedBetaTrace env U Γ type expression expression
  | next (head : HeadBeta first middle) (equal : env.IsDefEq U Γ first middle type)
      (tail : TypedBetaTrace env U Γ type middle last) : TypedBetaTrace env U Γ type first last

theorem TypedBetaTrace.trans (left : TypedBetaTrace env U Γ type first middle)
    (right : TypedBetaTrace env U Γ type middle last) : TypedBetaTrace env U Γ type first last := by
  induction left with
  | refl => exact right
  | next head equal _ ih => exact .next head equal (ih right)

theorem TypedBetaTrace.single (head : HeadBeta first last)
    (equal : env.IsDefEq U Γ first last type) : TypedBetaTrace env U Γ type first last :=
  .next head equal (.refl equal.hasType.2)

theorem TypedBetaTrace.cast (path : TypeConversion env U Γ A B)
    (trace : TypedBetaTrace env U Γ A first last) : TypedBetaTrace env U Γ B first last := by
  induction trace with
  | refl typed => exact .refl (path.cast typed)
  | next head equal _ ih => exact .next head (path.cast equal) ih

theorem TypedBetaTrace.weak (henv : env.Ordered) (W : Ctx.Lift' ρ Γ Δ)
    (trace : TypedBetaTrace env U Γ type first last) :
    TypedBetaTrace env U Δ (type.lift' ρ) (first.lift' ρ) (last.lift' ρ) := by
  induction trace with
  | refl typed => exact .refl (typed.weak' henv W)
  | next head equal _ ih => exact .next (head.lift ρ) (equal.weak' henv W) ih

theorem TypedBetaTrace.app (argument : env.HasType U Γ a A)
    (trace : TypedBetaTrace env U Γ (.forallE A B) first last) :
    TypedBetaTrace env U Γ (B.inst a) (.app first a) (.app last a) := by
  induction trace with
  | refl typed => exact .refl (.appDF typed argument)
  | next head equal _ ih => exact .next (head.app a) (.appDF equal argument) ih

theorem TypedBetaTrace.open (henv : env.Ordered) (domains : List VExpr)
    (trace : TypedBetaTrace env U Γ (wrapForalls domains type) first last) :
    TypedBetaTrace env U (domains.reverse ++ Γ) type
      (nativeEtaBody domains.length first) (nativeEtaBody domains.length last) := by
  induction domains generalizing Γ first last with
  | nil => exact trace
  | cons A domains ih =>
    have lifted := trace.weak henv (Ctx.Lift'.skip (A := A) Ctx.Lift'.refl)
    simp only [← lift_eq_lift', wrapForalls, List.foldr_cons, VExpr.lift, VExpr.liftN] at lifted
    have one := lifted.app (.bvar Lookup.zero)
    simp only [instN_bvar0] at one
    simpa only [List.length_cons, nativeEtaBody, List.reverse_cons,
      List.append_assoc, List.singleton_append, lift_eq_lift'] using ih one

private theorem prefixWF {env : VEnv} {U : Nat} {front Γ : List VExpr} (h : OnCtx (front ++ Γ) (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  induction front with
  | nil => exact h
  | cons _ _ ih => exact ih h.1

private theorem closeBody {env : VEnv} {U : Nat} {domains Γ : List VExpr} {body type : VExpr}
    (hContext : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (bodyTyped : env.HasType U (domains.reverse ++ Γ) body type) :
    env.HasType U Γ (wrapLams domains body) (wrapForalls domains type) := by
  induction domains generalizing Γ with
  | nil => exact bodyTyped
  | cons A domains ih =>
    have ht : OnCtx (domains.reverse ++ A :: Γ) (env.IsType U) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hContext
    obtain ⟨_, hA⟩ := (prefixWF ht).2
    exact .lam hA (ih ht (by simpa only [List.reverse_cons, List.append_assoc,
      List.singleton_append] using bodyTyped))

/-- The body is closed at its own natural type for this raw trace. An exact
declared-body conversion can subsequently cast every edge simultaneously. -/
theorem TypedBetaTrace.nativeRhs (henv : env.Ordered)
    (domains : List VExpr) (hContext : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (bodyTyped : env.HasType U (domains.reverse ++ Γ) body type) :
    TypedBetaTrace env U (domains.reverse ++ Γ) type
      (nativeEtaBody domains.length (wrapLams domains body)) body := by
  induction domains generalizing Γ with
  | nil => exact .refl bodyTyped
  | cons A domains ih =>
    have ht : OnCtx (domains.reverse ++ A :: Γ) (env.IsType U) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hContext
    have hb : env.HasType U (domains.reverse ++ A :: Γ) body type := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using bodyTyped
    have wrapped := closeBody ht hb
    have lifted := wrapped.weakN henv (Ctx.LiftN.succ (Ctx.LiftN.one (A := A)))
    have beta := IsDefEq.beta lifted (IsDefEq.bvar (Lookup.zero (Γ := Γ) (ty := A)))
    simp only [instN_bvar0] at beta
    have one : TypedBetaTrace env U (A :: Γ) (wrapForalls domains type)
        (.app (VExpr.lam A (wrapLams domains body)).lift (.bvar 0))
        (wrapLams domains body) :=
      .single (by simpa only [lift, liftN, instN_bvar0, mkApps, List.foldl_cons, List.foldl_nil] using
        (HeadBeta.contract (A := A.lift) (body := (wrapLams domains body).liftN 1 1)
          (argument := .bvar 0) (trailing := []))) beta
    have first := one.open henv domains
    have rest := ih ht hb
    simpa only [List.length_cons, nativeEtaBody, wrapLams, List.foldr_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append] using first.trans rest

private theorem mkApps_subst (f : VExpr) (args : List VExpr) (σ : Subst) :
    (mkApps f args).subst σ = mkApps (f.subst σ) (args.map (·.subst σ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

theorem HeadBeta.subst (step : HeadBeta first last) (σ : Subst) :
    HeadBeta (first.subst σ) (last.subst σ) := by
  induction step with
  | refl => exact .refl
  | apply _ ih => exact .apply ih
  | proj _ ih => exact .proj ih
  | @contract A body argument trailing =>
    simpa only [mkApps_subst, VExpr.subst, List.map_cons, subst_inst] using
      (HeadBeta.contract (A := A.subst σ) (body := body.subst σ.lift)
        (argument := argument.subst σ) (trailing := trailing.map (·.subst σ)))

theorem TypedBetaTrace.subst (henv : env.Ordered)
    (hTarget : OnCtx Δ (env.IsType U)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (trace : TypedBetaTrace env U Γ type first last) :
    TypedBetaTrace env U Δ (type.subst σ) (first.subst σ) (last.subst σ) := by
  induction trace with
  | refl typed => exact .refl (typed.subst henv W hTarget)
  | next head equal _ ih => exact .next (head.subst σ) (equal.subst henv W hTarget) ih

theorem TypedBetaTrace.firstTyped (trace : TypedBetaTrace env U Γ type first last) :
    env.HasType U Γ first type := by
  cases trace with
  | refl typed => exact typed
  | next _ equal _ => exact equal.hasType.1


end Lean4Lean.AnchoredSemantics
