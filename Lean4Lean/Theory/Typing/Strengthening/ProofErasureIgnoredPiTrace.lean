import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionObservations
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure

/-! # Type-head traces that ignore every application argument

The trace counts pending lambda arguments along a path ending at a literal Pi or sort.
It has no variable case and demands nothing of arguments or annotations.
Constant beta expansion preserves this stronger, substitution-stable trace.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- A finite function/body path reaches a Pi or sort after ignoring `n` arguments.
The trace inspects neither lambda domains nor application arguments. -/
inductive IgnoredTypeHeadTrace : Bool → ProofShape → Nat → Prop where
  | pi : IgnoredTypeHeadTrace true (.forallE A B) 0
  | sort : IgnoredTypeHeadTrace false (.sort u) 0
  | lam : IgnoredTypeHeadTrace isPi b n → IgnoredTypeHeadTrace isPi (.lam A b) (n + 1)
  | app : IgnoredTypeHeadTrace isPi f (n + 1) → IgnoredTypeHeadTrace isPi (.app f a) n

/-- The Pi instance of the shared ignored-argument trace. -/
abbrev IgnoredPiTrace := IgnoredTypeHeadTrace true

/-- The sort instance of the shared ignored-argument trace. -/
abbrev IgnoredSortTrace := IgnoredTypeHeadTrace false

/-- Arbitrary raw substitution preserves a trace because no variable is used
to supply the observed type head. -/
theorem IgnoredTypeHeadTrace.subst (H : IgnoredTypeHeadTrace isPi a n) : IgnoredTypeHeadTrace isPi (a.subst σ) n := by
  induction H generalizing σ with
  | pi => exact .pi
  | sort => exact .sort
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih

/-- Inserting binders preserves the same ignored-argument count. -/
theorem IgnoredTypeHeadTrace.liftN (H : IgnoredTypeHeadTrace isPi a n) : IgnoredTypeHeadTrace isPi (a.liftN k i) n := by
  induction H generalizing i with
  | pi => exact .pi
  | sort => exact .sort
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih

/-- Binder insertion cannot create a trace absent from the original syntax. -/
theorem IgnoredTypeHeadTrace.of_liftN (H : IgnoredTypeHeadTrace isPi (a.liftN k i) n) : IgnoredTypeHeadTrace isPi a n := by
  induction a generalizing i n with
  | proof | bvar | const | proj => cases H
  | sort => cases H; exact .sort
  | app f a ihf _ => cases H with | app H => exact .app (ihf H)
  | lam A b _ ihb => cases H with | lam H => exact .lam (ihb H)
  | forallE => cases H; exact .pi

/-- Root beta contracts the unused control demand; all compatible beta paths
preserve the trace at exactly the same remaining arity. -/
theorem IgnoredTypeHeadTrace.beta (R : BetaRed a b) (H : IgnoredTypeHeadTrace isPi a n) : IgnoredTypeHeadTrace isPi b n := by
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
theorem IgnoredTypeHeadTrace.not_primitiveHead (H : IgnoredTypeHeadTrace isPi a n) : ¬ PrimitiveHead a := by
  induction H with
  | pi | sort | lam => exact id
  | app _ ih => exact ih

/-- Constant expansion adds an unused lambda and immediately supplies its
ignored argument. It preserves even raw traces without source typings. -/
theorem IgnoredTypeHeadTrace.constantExpansion (H : IgnoredTypeHeadTrace isPi a n) :
    IgnoredTypeHeadTrace isPi (constantExpansion a) n := .app (.lam H.liftN)

/-- Eta preserves a trace whenever the demand asks for at least one argument.
Both retained and erased eta arguments are ignored by the trace. -/
theorem IgnoredTypeHeadTrace.eta_iff (HE : EtaHead a b) :
    IgnoredTypeHeadTrace isPi a (n + 1) ↔ IgnoredTypeHeadTrace isPi b (n + 1) := by
  obtain ⟨A, arg, rfl, _⟩ := HE.shape
  constructor
  · intro H
    cases H with
    | lam H => cases H with | app H => exact H.of_liftN
  · intro H; exact .lam (.app H.liftN)

private def ignoredHeadDemand (isPi : Bool) : Nat → PureObservation.Ob
  | 0 => if isPi then .pi else .sort
  | n + 1 => .app [] (ignoredHeadDemand isPi n)

private theorem IgnoredTypeHeadTrace.observation (H : IgnoredTypeHeadTrace isPi a n) :
    HeadObservation S a (ignoredHeadDemand isPi n) := by
  induction H generalizing S with
  | pi => exact .pi
  | sort => exact .sort
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih (by simp)

/-- A trace with no pending arguments exposes a literal Pi by finite beta.
Its components need not normalize, and all original annotations are retained. -/
theorem IgnoredPiTrace.expose (H : IgnoredPiTrace a 0) :
    ∃ A B, BetaRed a (.forallE A B) :=
  (H.observation (S := fun _ _ => False)).pi_exposure

/-- A zero-arity sort trace exposes a literal universe by finite beta. -/
theorem IgnoredSortTrace.expose (H : IgnoredSortTrace a 0) :
    ∃ u, BetaRed a (.sort u) :=
  (H.observation (S := fun _ _ => False)).sort_exposure

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
theorem IgnoredTypeHeadTrace.compute
    (htrace : ∀ {Δ a b n}, Step Δ a b → IgnoredTypeHeadTrace isPi a n → IgnoredTypeHeadTrace isPi b n)
    (R : ScopedCompute Step Δ a b) (H : IgnoredTypeHeadTrace isPi a n) : IgnoredTypeHeadTrace isPi b n := by
  induction R generalizing n with
  | base R => exact htrace R H
  | beta R => exact H.beta R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ih _ => cases H with | app H => exact .app (ih H)
  | proj => cases H
  | lam _ _ _ ih => cases H with | lam H => exact .lam (ih H)
  | forallE => cases H; exact .pi

end Lean4Lean.VEnv.Strengthening.ProofShape
