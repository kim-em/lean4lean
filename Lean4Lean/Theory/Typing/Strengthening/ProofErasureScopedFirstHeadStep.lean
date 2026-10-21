import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-! # The first primitive at a constant spine

A computation that loses a constant head must contract a prefix of that spine.
Before the first such occurrence, only its supplied arguments compute. The
witness retains those argument paths and the original prefix length, so a
later decoder can inspect the primitive's guard without assuming that the
whole reduction is a single head step.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-- A primitive contracts a prefix after componentwise computation of exactly
the originally supplied prefix arguments. The unsupplied suffix is unrestricted. -/
def ScopedHeadOccurrence
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (c : Name) (ls : List VLevel) (args : List ProofShape) : Prop :=
  ∃ k changed out, k ≤ args.length ∧
    List.Forall₂ (ScopedCompute Step Δ) (args.take k) changed ∧
    Step Δ (mkApps (.const c ls) changed) out

/-- Either the original constant spine survives by componentwise computation,
or a primitive occurred at one of its prefixes. No inertness, normalization,
typing, or closure assumptions on the primitive relation are required. -/
theorem ScopedCompute.const_spine_or_head
    (R : ScopedCompute Step Δ (mkApps (.const c ls) args) out) :
    (∃ args', out = mkApps (.const c ls) args' ∧
      List.Forall₂ (ScopedCompute Step Δ) args args') ∨
    ScopedHeadOccurrence Step Δ c ls args := by
  generalize E : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base H =>
    refine .inr ⟨args.length, args, _, Nat.le_refl _, ?_, E ▸ H⟩
    rw [List.take_length]
    exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.const_spine
    exact .inl ⟨args', HE, HA.imp (fun _ _ h => .beta h)⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ E with ⟨args₁, rfl, H₁⟩ | hit
    · rcases ih₂ rfl with ⟨args₂, HE, H₂⟩ | ⟨k, changed, out, hk, HC, HS⟩
      · exact .inl ⟨args₂, HE,
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') H₁ H₂⟩
      · exact .inr ⟨k, changed, out, H₁.length_eq.symm ▸ hk,
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h')
            (List.forall₂_take H₁ k) HC, HS⟩
    · exact .inr hit
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    rcases ihf rfl with ⟨args', rfl, H⟩ | ⟨k, changed, out, hk, HC, HS⟩
    · exact .inl ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
    · refine .inr ⟨k, changed, out, by simp only [List.length_append, List.length_singleton]; omega,
        ?_, HS⟩
      rwa [List.take_append_of_le_length hk]
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

/-- Exposing any different head forces an actual primitive at a computed
prefix of the initial spine. Primitive steps inside arguments do not suffice. -/
theorem ScopedCompute.head_occurrence
    (R : ScopedCompute Step Δ (mkApps (.const c ls) args) out)
    (Hout : constHead out ≠ some c) : ScopedHeadOccurrence Step Δ c ls args := by
  rcases R.const_spine_or_head with ⟨args', rfl, _⟩ | hit
  · exact (Hout (constHead_mkApps _ _)).elim
  · exact hit

end Lean4Lean.VEnv.Strengthening.ProofShape
