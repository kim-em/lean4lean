import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionObservations
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure

/-! # Pi traces that ignore every application argument

The trace counts pending lambda arguments along a path ending at a literal Pi.
It has no variable case and demands nothing of arguments or annotations.
Constant beta expansion preserves this stronger, substitution-stable trace.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- A finite function/body path reaches a Pi after ignoring `n` arguments.
The trace inspects neither lambda domains nor application arguments. -/
inductive IgnoredPiTrace : ProofShape → Nat → Prop where
  | pi : IgnoredPiTrace (.forallE A B) 0
  | lam : IgnoredPiTrace b n → IgnoredPiTrace (.lam A b) (n + 1)
  | app : IgnoredPiTrace f (n + 1) → IgnoredPiTrace (.app f a) n

/-- Arbitrary raw substitution preserves a trace because no variable is used
to supply the observed Pi head. -/
theorem IgnoredPiTrace.subst (H : IgnoredPiTrace a n) : IgnoredPiTrace (a.subst σ) n := by
  induction H generalizing σ with
  | pi => exact .pi
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih

/-- Inserting binders preserves the same ignored-argument count. -/
theorem IgnoredPiTrace.liftN (H : IgnoredPiTrace a n) : IgnoredPiTrace (a.liftN k i) n := by
  induction H generalizing i with
  | pi => exact .pi
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih

/-- Binder insertion cannot create a trace absent from the original syntax. -/
theorem IgnoredPiTrace.of_liftN (H : IgnoredPiTrace (a.liftN k i) n) : IgnoredPiTrace a n := by
  induction a generalizing i n with
  | proof | bvar | sort | const | proj => cases H
  | app f a ihf _ => cases H with | app H => exact .app (ihf H)
  | lam A b _ ihb => cases H with | lam H => exact .lam (ihb H)
  | forallE => cases H; exact .pi

/-- Root beta contracts the unused control demand; all compatible beta paths
preserve the trace at exactly the same remaining arity. -/
theorem IgnoredPiTrace.beta (R : BetaRed a b) (H : IgnoredPiTrace a n) : IgnoredPiTrace b n := by
  induction R generalizing n with
  | refl => exact H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | beta =>
    cases H with
    | app H =>
      cases H with
      | lam H => simpa only [inst_eq_subst, Subst.liftN] using H.subst (σ := Subst.one _)
  | app _ _ ih _ => cases H with | app H => exact .app (ih H)
  | proj => cases H
  | lam _ _ _ ih => cases H with | lam H => exact .lam (ih H)
  | forallE => cases H; exact .pi

/-- Constant and projection heads cannot carry this observation. -/
theorem IgnoredPiTrace.not_primitiveHead (H : IgnoredPiTrace a n) : ¬ PrimitiveHead a := by
  induction H with
  | pi | lam => exact id
  | app _ ih => exact ih

/-- Constant expansion adds an unused lambda and immediately supplies its
ignored argument. It preserves even raw traces without source typings. -/
theorem IgnoredPiTrace.constantExpansion (H : IgnoredPiTrace a n) :
    IgnoredPiTrace (constantExpansion a) n := .app (.lam H.liftN)

/-- Eta preserves a trace whenever the demand asks for at least one argument.
Both retained and erased eta arguments are ignored by the trace. -/
theorem IgnoredPiTrace.eta_iff (HE : EtaHead a b) :
    IgnoredPiTrace a (n + 1) ↔ IgnoredPiTrace b (n + 1) := by
  obtain ⟨A, arg, rfl, _⟩ := HE.shape
  constructor
  · intro H
    cases H with
    | lam H => cases H with | app H => exact H.of_liftN
  · intro H; exact .lam (.app H.liftN)

private def ignoredPiDemand : Nat → PureObservation.Ob
  | 0 => .pi
  | n + 1 => .app [] (ignoredPiDemand n)

private theorem IgnoredPiTrace.observation (H : IgnoredPiTrace a n) :
    HeadObservation S a (ignoredPiDemand n) := by
  induction H generalizing S with
  | pi => exact .pi
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih (by simp)

/-- A trace with no pending arguments exposes a literal Pi by finite beta.
Its components need not normalize, and all original annotations are retained. -/
theorem IgnoredPiTrace.expose (H : IgnoredPiTrace a 0) :
    ∃ A B, BetaRed a (.forallE A B) :=
  (H.observation (S := fun _ _ => False)).pi_exposure

/-- Context-independent primitives allow exact recontextualization of a path,
including paths under changing lambda annotations. -/
theorem ScopedCompute.recontext_independent
    (hctx : ∀ {Δ Δ' a b}, Step Δ a b → Step Δ' a b)
    (R : ScopedCompute Step Δ a b) : ScopedCompute Step Δ' a b := by
  induction R generalizing Δ' with
  | base H => exact .base (hctx H)
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Primitive trace preservation extends to the whole compatible computation
relation. Binder contexts need not stay fixed along the path. -/
theorem IgnoredPiTrace.compute
    (htrace : ∀ {Δ a b n}, Step Δ a b → IgnoredPiTrace a n → IgnoredPiTrace b n)
    (R : ScopedCompute Step Δ a b) (H : IgnoredPiTrace a n) : IgnoredPiTrace b n := by
  induction R generalizing n with
  | base R => exact htrace R H
  | beta R => exact H.beta R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ih _ => cases H with | app H => exact .app (ih H)
  | proj => cases H
  | lam _ _ _ ih => cases H with | lam H => exact .lam (ih H)
  | forallE => cases H; exact .pi

end Lean4Lean.VEnv.Strengthening.ProofShape
