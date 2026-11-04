import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Pi readout with retained dependent component computations

A certificate records a beta-exposed Pi and paths for both its components in
the original scopes. Beta confluence preserves this information after further
beta reduction. Expanded roots and evolved identity wrappers preserve it too.
Coverage of arbitrary compatible expanded paths is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-- A Pi can be beta-exposed while retaining computation from the assigned
domain and codomain. The codomain path stays under the original domain A. -/
def PiReadout (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A B out : ProofShape) : Prop :=
  ∃ X Y, ScopedCompute Step Δ A X ∧ ScopedCompute Step (A :: Δ) B Y ∧
    BetaRed out (.forallE X Y)

/-- Compatible computation of the two displayed components starts a readout. -/
theorem PiReadout.parts
    (RA : ScopedCompute Step Δ A X) (RB : ScopedCompute Step (A :: Δ) B Y) :
    PiReadout Step Δ A B (.forallE X Y) := ⟨X, Y, RA, RB, .refl⟩

/-- A literal Pi has its original component computations. -/
theorem PiReadout.refl : PiReadout Step Δ A B (.forallE A B) := .parts .refl .refl

/-- Enlarging the component relation keeps the exact readout path. -/
theorem PiReadout.mono (H : PiReadout Step Δ A B out)
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b) : PiReadout Step' Δ A B out := by
  obtain ⟨X, Y, RA, RB, R⟩ := H
  exact ⟨X, Y, RA.mono hstep, RB.mono hstep, R⟩

/-- A beta predecessor has the same selected components and histories. -/
theorem PiReadout.beta_back (H : PiReadout Step Δ A B out) (R : BetaRed source out) :
    PiReadout Step Δ A B source := by
  obtain ⟨X, Y, RA, RB, RBeta⟩ := H
  exact ⟨X, Y, RA, RB, R.trans RBeta⟩

/-- Further beta reduction retains the component paths by raw beta confluence.
This permits arbitrary beta interleavings, without normalization or typing. -/
theorem PiReadout.beta (H : PiReadout Step Δ A B source) (R : BetaRed source out) :
    PiReadout Step Δ A B out := by
  obtain ⟨X, Y, RA, RB, RBeta⟩ := H
  obtain ⟨shared, RO, RP⟩ := R.raw_confluent RBeta
  obtain ⟨X', Y', rfl, RX, RY⟩ := beta_forallE_parts RP
  exact ⟨X', Y', RA.trans (.beta RX), RB.trans (.beta RY), RO⟩

/-- A readout excludes a constant/projection head before beta evaluation. -/
theorem PiReadout.not_primitiveHead (H : PiReadout Step Δ A B source) : ¬ PrimitiveHead source := by
  obtain ⟨X, Y, _, _, R⟩ := H
  have HP : HeadObservation (fun _ _ => False) (.forallE X Y) .pi := PureObservation.Obs.pi
  exact (HP.beta_backward R).not_primitiveHead

/-- Constant expansion preserves all selected component information. -/
theorem PiReadout.constant_expansion (H : PiReadout Step Δ A B source) :
    PiReadout Step Δ A B (constantExpansion source) := H.beta_back (constantExpansion_beta _)

/-- Both component paths give computed comparisons at their original scopes. -/
theorem PiReadout.select [Params] (H : PiReadout Step Δ A B out) :
    ∃ X Y, BetaRed out (.forallE X Y) ∧
      ComputedJointCompare Step Δ false A X ∧
      ComputedJointCompare Step (A :: Δ) false B Y := by
  obtain ⟨X, Y, RA, RB, R⟩ := H
  exact ⟨X, Y, R, .compute RA .refl (.leaf .refl), .compute RB .refl (.leaf .refl)⟩

/-- Existing native evidence at the assigned Pi can select the exposed Pi
using only its component paths. The surrounding wrapper history contributes
no stage cost and need not itself be a native output. -/
theorem PiReadout.native [Params] (H : PiReadout Step Δ A B out)
    (RN : ScopedTypeRecovery Step Δ source (.forallE A B)) :
    ∃ X Y, ScopedTypeRecovery Step Δ source (.forallE X Y) ∧
      BetaRed out (.forallE X Y) ∧
      ScopedCompute Step Δ A X ∧ ScopedCompute Step (A :: Δ) B Y := by
  obtain ⟨X, Y, RA, RB, R⟩ := H
  exact ⟨X, Y, RN.convert (.forallE RA RB), R, RA, RB⟩

end ProofShape
variable [Params]

/-- Any expanded primitive at the outer root preserves a Pi readout. Opaque
primitive heads are impossible; controlled expansions are beta predecessors.
The root's guard stage and scope need not match the component computations. -/
theorem piReadout_expansion_root
    (H : PiReadout Step Δ A B source)
    (R : ErasedExpansionStage D stage Δroot source out) : PiReadout Step Δ A B out := by
  have hobs : HeadObservation (fun _ _ => False) source .pi := by
    obtain ⟨X, Y, _, _, RB⟩ := H
    have HP : HeadObservation (fun _ _ => False) (.forallE X Y) .pi := PureObservation.Obs.pi
    exact HP.beta_backward RB
  induction stage with
  | zero =>
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => cases PureObservation.Obs.sort_inv hobs
      | const => exact (PureObservation.Obs.empty_const_false hobs).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    rcases R with R | R | R | R
    · exact ih R
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R
      apply H.beta_back
      simpa only [ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
        (ProofShape.BetaRed.beta (b := .bvar 0))

/-- Unbounded finite guard depth still preserves an existing Pi origin. -/
theorem piReadout_expansion_union_root
    (H : PiReadout Step Δ A B source)
    (R : ErasedExpansionUnion D Δroot source out) : PiReadout Step Δ A B out := by
  obtain ⟨stage, R⟩ := R
  exact piReadout_expansion_root H R

/-- A whole computed identity function can wrap the selected Pi without losing
its domain or dependent-codomain computation paths. -/
theorem piReadout_computed_identity
    (H : PiReadout Step Δ A B payload)
    (RF : ScopedCompute (ErasedExpansionUnion D) Δf (.lam T (.bvar 0)) outF) :
    PiReadout Step Δ A B (.app outF payload) :=
  H.beta_back (expansion_union_identity_behavior RF payload)

/-- The same information remains after the wrapper's outer beta step. -/
theorem piReadout_computed_identity_contractum
    (H : PiReadout Step Δ A B payload)
    (RB : ScopedCompute (ErasedExpansionUnion D) Δb (.bvar 0) outB) :
    PiReadout Step Δ A B (outB.inst payload) :=
  H.beta_back (expansion_union_identity_contractum_beta RB payload)

/-- Arbitrarily many whole-root expanded steps interleaved with compatible beta
retain the component histories. General scoped congruence is a separate gap. -/
theorem piReadout_root_beta_path
    (H : PiReadout Step Δ A B source)
    (R : ReflTransGen (fun a b => ErasedExpansionUnion D Δroot a b ∨ ProofShape.BetaRed a b) source out) :
    PiReadout Step Δ A B out := by
  induction R with
  | rfl => exact H
  | tail _ R ih =>
    rcases R with R | R
    · exact piReadout_expansion_union_root ih R
    · exact ih.beta R

end Lean4Lean.VEnv.Strengthening
