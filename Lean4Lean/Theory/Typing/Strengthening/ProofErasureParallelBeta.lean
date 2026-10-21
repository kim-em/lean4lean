import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution
import Lean4Lean.Theory.Typing.Strengthening.DeclarationConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-! # Parallel beta development of annotated proof shapes

A step contracts any selected source beta redexes, including their selected
body and argument redexes. Substitution duplicates developments, not an
unbounded normalization process. Complete development gives the diamond.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- One parallel beta development; newly created redexes need not contract. -/
inductive BetaPar : ProofShape → ProofShape → Prop where
  | proof : BetaPar .proof .proof
  | bvar : BetaPar (.bvar i) (.bvar i)
  | sort : BetaPar (.sort u) (.sort u)
  | const : BetaPar (.const c ls) (.const c ls)
  | app : BetaPar f f' → BetaPar a a' → BetaPar (.app f a) (.app f' a')
  | lam : BetaPar A A' → BetaPar b b' → BetaPar (.lam A b) (.lam A' b')
  | forallE : BetaPar A A' → BetaPar B B' → BetaPar (.forallE A B) (.forallE A' B')
  | proj : BetaPar m m' → BetaPar (.proj s i m) (.proj s i m')
  | beta : BetaPar b b' → BetaPar a a' → BetaPar (.app (.lam A b) a) (b'.inst a')

/-- Selecting no redexes is a parallel development. -/
theorem BetaPar.refl (e : ProofShape) : BetaPar e e := by
  induction e with
  | proof => exact .proof
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | proj _ _ _ ih => exact .proj ih

/-- Parallel developments weaken through arbitrary binder insertions. -/
theorem BetaPar.liftN (R : BetaPar e e') : BetaPar (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | proof => exact .proof
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | proj _ ih => exact .proj ih
  | @beta b b' a a' A _ _ ih₁ ih₂ =>
    simpa only [Nat.add_zero] using
      (liftN_instN b' a' n k 0).symm ▸
        (BetaPar.beta (A := A.liftN n k) (ih₁ (k := k+1)) (ih₂ (k := k)))

/-- Parallel substitution copies the selected developments at every variable
occurrence, including beneath a simultaneously contracted beta redex. -/
theorem BetaPar.subst (R : BetaPar e e') (H : ∀ i, BetaPar (σ i) (τ i)) :
    BetaPar (e.subst σ) (e'.subst τ) := by
  have hlift {σ τ : Subst} (H : ∀ i, BetaPar (σ i) (τ i)) :
      ∀ i, BetaPar (σ.lift i) (τ.lift i) := by
    intro i
    cases i with
    | zero => exact .bvar
    | succ i => exact (H i).liftN
  induction R generalizing σ τ with
  | proof => exact .proof
  | bvar => exact H _
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih₁ ih₂ => exact .app (ih₁ H) (ih₂ H)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ H) (ih₂ (hlift H))
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ H) (ih₂ (hlift H))
  | proj _ ih => exact .proj (ih H)
  | beta _ _ ih₁ ih₂ => rw [subst_inst]; exact .beta (ih₁ (hlift H)) (ih₂ H)

/-- Parallel body and argument developments instantiate in one parallel step. -/
theorem BetaPar.inst (R : BetaPar e e') (H : BetaPar a a') :
    BetaPar (e.inst a) (e'.inst a') := by
  rw [inst_eq_subst, inst_eq_subst]
  apply R.subst
  intro i
  cases i with
  | zero => exact H
  | succ i => exact .bvar

/-- A parallel development serializes into ordinary finite beta reduction. -/
theorem BetaPar.toBeta (R : BetaPar e e') : BetaRed e e' := by
  induction R with
  | proof | bvar | sort | const => exact .refl
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | proj _ ih => exact .proj ih
  | beta _ _ ih₁ ih₂ => exact (BetaRed.app (.lam .refl ih₁) ih₂).trans .beta

private def betaDevelop : ProofShape → ProofShape
  | .proof => .proof
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .app (.lam _ b) a => (betaDevelop b).inst (betaDevelop a)
  | .app f a => .app (betaDevelop f) (betaDevelop a)
  | .lam A b => .lam (betaDevelop A) (betaDevelop b)
  | .forallE A B => .forallE (betaDevelop A) (betaDevelop B)
  | .proj s i m => .proj s i (betaDevelop m)

private theorem triangle (R : BetaPar e e') : BetaPar e' (betaDevelop e) := by
  induction R with
  | proof => exact .proof
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | @app f f' a a' Rf Ra ihf iha =>
    cases f with
    | lam A b =>
      cases Rf with
      | lam RA Rb =>
        cases ihf with
        | lam _ ihb => exact .beta ihb iha
    | proof | bvar | sort | const | app | forallE | proj => exact .app ihf iha
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | proj _ ih => exact .proj ih
  | beta _ _ ih₁ ih₂ => exact ih₁.inst ih₂

/-- Any two parallel developments reach the source's complete development in
one further parallel step. This gives a diamond without normalization. -/
theorem BetaPar.diamond (R : BetaPar e a) (S : BetaPar e b) :
    ∃ out, BetaPar a out ∧ BetaPar b out :=
  ⟨betaDevelop e, triangle R, triangle S⟩

open private const_spine_app from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-- A parallel beta development of a constant spine develops just its supplied
arguments, each in one parallel step. -/
theorem BetaPar.const_spine (R : BetaPar (mkApps (.const c ls) args) out) :
    ∃ args', out = mkApps (.const c ls) args' ∧ List.Forall₂ BetaPar args args' := by
  generalize E : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | const =>
    cases args using List.snoc_induction with
    | nil => cases E; exact ⟨[], rfl, .nil⟩
    | snoc args a => rw [mkApps_snoc] at E; cases E
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proof | bvar | sort | proj | lam | forallE | beta =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

end Lean4Lean.VEnv.Strengthening.ProofShape
