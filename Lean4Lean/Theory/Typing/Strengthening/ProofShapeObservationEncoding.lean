import Lean4Lean.Theory.Typing.Strengthening.PureObservationForward
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveHeads

/-! # An operational encoding of proof shapes for finite observations

The proof marker is encoded as an opaque constant. This is not an original
well-typed representative and is not used to reflect equality. Beta paths do
reflect back to the exact source proof shape, including all annotations.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Syntax encoding with an opaque proof marker. Actual constant names receive
a tag to distinguish them from the marker. Neither has an interpretation here. -/
def toObservationExpr : ProofShape → VExpr
  | .proof => .const .anonymous []
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const (.str c "observation") ls
  | .app f a => .app f.toObservationExpr a.toObservationExpr
  | .proj s i m => .proj s i m.toObservationExpr
  | .lam A b => .lam A.toObservationExpr b.toObservationExpr
  | .forallE A B => .forallE A.toObservationExpr B.toObservationExpr

/-- The constant tag makes this a syntactically injective encoding, including
at the proof marker. This does not assert reflection of semantic equality. -/
theorem toObservationExpr_injective : Function.Injective toObservationExpr := by
  intro a b H
  induction a generalizing b <;> cases b <;> simp_all [toObservationExpr] <;> grind

/-- Encoding commutes with arbitrary binder insertion. -/
theorem toObservationExpr_liftN (a : ProofShape) :
    (a.liftN n k).toObservationExpr = a.toObservationExpr.liftN n k := by
  induction a generalizing k <;> simp only [liftN, toObservationExpr, VExpr.liftN, *]

/-- Encoding commutes with single substitution at every binder depth. -/
theorem toObservationExpr_inst (b a : ProofShape) :
    (b.inst a k).toObservationExpr = b.toObservationExpr.inst a.toObservationExpr k := by
  induction b generalizing k with
  | bvar i =>
    simp only [inst, VExpr.inst, VExpr.instVar, toObservationExpr]
    split
    · rfl
    · split
      · exact toObservationExpr_liftN a
      · rfl
  | proof | sort | const => rfl
  | app | proj | lam | forallE => simp only [inst, toObservationExpr, VExpr.inst, *]

/-- An encoded application has an actual application-shaped preimage. -/
theorem toObservationExpr_app_inv {a : ProofShape} (E : a.toObservationExpr = .app f x) :
    ∃ f' x', a = .app f' x' ∧ f'.toObservationExpr = f ∧ x'.toObservationExpr = x := by
  cases a <;> cases E
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- Lambda annotations and bodies are retained by the encoding. -/
theorem toObservationExpr_lam_inv {a : ProofShape} (E : a.toObservationExpr = .lam A b) :
    ∃ A' b', a = .lam A' b' ∧ A'.toObservationExpr = A ∧ b'.toObservationExpr = b := by
  cases a <;> cases E
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- Pi heads reflect to actual proof-shape Pi heads. -/
theorem toObservationExpr_forallE_inv {a : ProofShape} (E : a.toObservationExpr = .forallE A B) :
    ∃ A' B', a = .forallE A' B' ∧ A'.toObservationExpr = A ∧ B'.toObservationExpr = B := by
  cases a <;> cases E
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- Projection sources retain their original projection metadata. -/
theorem toObservationExpr_proj_inv {a : ProofShape} (E : a.toObservationExpr = .proj s i m) :
    ∃ m', a = .proj s i m' ∧ m'.toObservationExpr = m := by
  cases a <;> cases E
  exact ⟨_, rfl, rfl⟩

/-- Raw beta reduction maps to ordinary untyped beta reduction. -/
theorem BetaRed.toObservationExpr (R : BetaRed a b) :
    VExpr.BetaRed a.toObservationExpr b.toObservationExpr := by
  induction R with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta => rw [toObservationExpr_inst]; exact .beta
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- Every beta computation of an encoded source has an exact raw beta replay.
No inverse interpretation or injectivity at the opaque proof constant is needed. -/
theorem beta_of_toObservationExpr (R : VExpr.BetaRed a.toObservationExpr out) :
    ∃ b, BetaRed a b ∧ b.toObservationExpr = out := by
  generalize E : a.toObservationExpr = source at R
  induction R generalizing a with
  | refl => exact ⟨a, .refl, E⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b, R₁, E₁⟩ := ih₁ E
    obtain ⟨c, R₂, E₂⟩ := ih₂ E₁
    exact ⟨c, R₁.trans R₂, E₂⟩
  | beta =>
    obtain ⟨f, x, rfl, Ef, Ex⟩ := toObservationExpr_app_inv E
    obtain ⟨A, b, rfl, EA, Eb⟩ := toObservationExpr_lam_inv Ef
    exact ⟨b.inst x, .beta, by rw [toObservationExpr_inst, Eb, Ex]⟩
  | app _ _ ihf ihx =>
    obtain ⟨f, x, rfl, Ef, Ex⟩ := toObservationExpr_app_inv E
    obtain ⟨f', Rf, Ef'⟩ := ihf Ef
    obtain ⟨x', Rx, Ex'⟩ := ihx Ex
    exact ⟨.app f' x', .app Rf Rx, congr (congrArg VExpr.app Ef') Ex'⟩
  | proj _ ihm =>
    obtain ⟨m, rfl, Em⟩ := toObservationExpr_proj_inv E
    obtain ⟨m', Rm, Em'⟩ := ihm Em
    exact ⟨.proj _ _ m', .proj Rm, congrArg (VExpr.proj _ _) Em'⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, EA, Eb⟩ := toObservationExpr_lam_inv E
    obtain ⟨A', RA, EA'⟩ := ihA EA
    obtain ⟨b', Rb, Eb'⟩ := ihb Eb
    exact ⟨.lam A' b', .lam RA Rb, congr (congrArg VExpr.lam EA') Eb'⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, EA, EB⟩ := toObservationExpr_forallE_inv E
    obtain ⟨A', RA, EA'⟩ := ihA EA
    obtain ⟨B', RB, EB'⟩ := ihB EB
    exact ⟨.forallE A' B', .forallE RA RB, congr (congrArg VExpr.forallE EA') EB'⟩

/-- Operational beta paths between encoded endpoints reflect exactly, using
the constant tag to keep proof markers distinct from genuine constants. -/
theorem beta_toObservationExpr_iff :
    VExpr.BetaRed a.toObservationExpr b.toObservationExpr ↔ BetaRed a b := by
  constructor
  · intro R
    obtain ⟨out, RB, E⟩ := beta_of_toObservationExpr R
    exact toObservationExpr_injective E ▸ RB
  · exact BetaRed.toObservationExpr

end Lean4Lean.VEnv.Strengthening.ProofShape
