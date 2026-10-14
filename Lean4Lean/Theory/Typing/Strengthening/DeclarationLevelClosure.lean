import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadTyping

/-! # Universe-stable closed declaration computation

Saturating a collection of closed constant equations under equality of its
well-formed level arguments preserves soundness. Right-hand sides are retained
exactly; ordinary universe conversion aligns the new constant instance.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {D : Definitions} {env : VEnv}

/-- Universe changes at the constant preserve availability of each equation. -/
def Definitions.LevelStable (D : Definitions) (U : Nat) : Prop :=
  ∀ {c ls ls' rhs}, D.unfolds c ls rhs → (∀ l ∈ ls', l.WF U) →
    List.Forall₂ (· ≈ ·) ls ls' → D.unfolds c ls' rhs

/-- Add only equivalent well-formed level instances of existing closed equations. -/
def Definitions.levelClosure (D : Definitions) (U : Nat) : Definitions where
  unfolds c ls rhs := ∃ ls0, D.unfolds c ls0 rhs ∧
    (∀ l ∈ ls, l.WF U) ∧ List.Forall₂ (· ≈ ·) ls0 ls
  closed := by rintro _ _ _ ⟨_, H, _⟩; exact D.closed H

theorem Definitions.levelClosure_stable : (D.levelClosure U).LevelStable U := by
  rintro c ls ls' rhs ⟨ls0, H, _, he⟩ hw he'
  exact ⟨ls0, H, hw, he.trans (fun _ _ _ h => h.trans) he'⟩

/-- Every well-formed original level instance remains available. -/
theorem Definitions.unfolds_levelClosure (H : D.unfolds c ls rhs)
    (hw : ∀ l ∈ ls, l.WF U) : (D.levelClosure U).unfolds c ls rhs :=
  ⟨ls, H, hw, .rfl (fun _ _ => rfl)⟩

/-- Actual source typing suffices to align the new constant's level instance. -/
theorem Definitions.levelClosure_sound (henv : env.WF) (hs : D.Sound env U) :
    (D.levelClosure U).Sound env U := by
  rintro Γ c ls rhs ⟨ls0, H, hw, he⟩
  obtain ⟨T, HT⟩ := hs [] c ls0 rhs H
  have hnil : OnCtx ([] : List VExpr) (env.IsType U) := trivial
  obtain ⟨ci, hc, hw0, hl⟩ := HT.hasType.1.const_inv henv hnil
  have HC : env.IsDefEqU U [] (.const c ls0) (.const c ls) :=
    ⟨_, .constDF hc hw0 hw hl he⟩
  have HR := ((HC.of_l henv hnil HT.hasType.1).symm.trans HT)
  exact ⟨_, HR.weak0 henv⟩

/-- Sound collections already have well-formed source levels, so saturation
retains all of their equations, without an additional source-side premise. -/
theorem Definitions.sound_in_levelClosure (henv : env.WF) (hs : D.Sound env U)
    (H : D.unfolds c ls rhs) : (D.levelClosure U).unfolds c ls rhs := by
  obtain ⟨_, HT⟩ := hs [] c ls rhs H
  have hnil : OnCtx ([] : List VExpr) (env.IsType U) := trivial
  obtain ⟨_, _, hw, _⟩ := HT.hasType.1.const_inv henv hnil
  exact Definitions.unfolds_levelClosure H hw

end Lean4Lean.VEnv.Strengthening.PureObservation
