import Lean4Lean.Theory.Typing.Strengthening.TypeHeadExtension
import Lean4Lean.Theory.Typing.Strengthening.IndexedEtaComputation

/-! # Indexed stages with cast-head type recovery

The previous indexed stages remain included. Additional eta and endpoint guards
may recover types through the sort-source cast extension of the preceding stage.
Those restricted type computations are not ordinary compatible term steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params] {C C' : List VExpr → VExpr → VExpr → Prop}

/-- A predecessor can drive ordinary indexed computation, or use cast-head
recovery for K guards, singleton guards and eta annotations. -/
def TypedIndexedNext (D : Definitions) (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (e out : VExpr) : Prop :=
  IndexedNextComputation D C Γ e out ∨
  GuardedKCompute D (RecoveredComparisonWith (TypeHeadExtension C) true) Γ e out ∨
  GuardedSingleton.PrefixStep (RecoveredComparisonWith (TypeHeadExtension C) true) Γ e out ∨
  TypedEtaStep (TypeHeadExtension C) Γ e out

/-- Sort-source replay is confined to recovery; every resulting ordinary step
has full source-typed descent. -/
theorem TypedIndexedNext.descends (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) :
    ComputeDescent (TypedIndexedNext D C) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  rcases R with R | R | R | R
  · exact IndexedNextComputation.descends heq hs hc R W hΓ hΓ' ht
  · obtain ⟨out, ho, H⟩ := R.descend heq hs
      (TypeHeadExtension.comparisonDescent heq hc) W hΓ hΓ'
    exact ⟨out, ho, H _ ht⟩
  · exact GuardedSingleton.PrefixStep.computeDescent heq
      (TypeHeadExtension.comparisonDescent heq hc) R W hΓ hΓ' ht
  · exact TypedEtaStep.computeDescent (TypeHeadExtension.typeDescent heq hc) R W hΓ hΓ' ht

/-- Each guard and eta certificate weakens using the same predecessor bound. -/
theorem TypedIndexedNext.weakens (heq : env.HasCanonicalEq) (hw : ComputeWeakening C) :
    ComputeWeakening (TypedIndexedNext D C) := by
  intro n k Γ Γ' e out W R
  have hwT : ComputeWeakening (TypeHeadExtension C) := TypeHeadExtension.weakening hw
  rcases R with R | R | R | R
  · exact .inl (IndexedNextComputation.weakens heq hw W R)
  · exact .inr (.inl (R.weakN (fun W H => H.weakN hwT W) W))
  · exact .inr (.inr (.inl (GuardedSingleton.PrefixStep.computeWeakening heq
      (fun W H => H.weakN hwT W) W R)))
  · exact .inr (.inr (.inr (TypedEtaStep.weakening hwT W R)))

/-- Enlarging the predecessor enlarges computations, guards and recovery. -/
theorem TypedIndexedNext.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (R : TypedIndexedNext D C Γ e out) : TypedIndexedNext D C' Γ e out := by
  rcases R with R | R | R | R
  · exact .inl (R.mono hC)
  · exact .inr (.inl (R.map_guards (fun H => H.mono (TypeHeadExtension.mono hC))))
  · exact .inr (.inr (.inl (R.map_guards (fun H => H.mono (TypeHeadExtension.mono hC)))))
  · exact .inr (.inr (.inr (R.mono (TypeHeadExtension.mono hC))))

/-- Finite simultaneous closure of indexed prefixes, guarded K and eta, with
type-restricted cast recovery available at each successor stage. -/
def TypedIndexedEtaCompute (D : Definitions) (kdepth : Nat) :
    Nat → List VExpr → VExpr → VExpr → Prop
  | 0 => CertifiedKCompute D kdepth
  | stage + 1 => RecoveredEtaWith (TypedIndexedNext D (TypedIndexedEtaCompute D kdepth stage))

/-- Every stage has ordinary computation descent. -/
theorem TypedIndexedEtaCompute.computeDescent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ∀ stage, ComputeDescent (TypedIndexedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact CertifiedKCompute.computeDescent heq hs
  | succ stage ih => exact RecoveredEtaWith.computeDescent (TypedIndexedNext.descends heq hs ih)

/-- Every stage weakens without increasing the stage. -/
theorem TypedIndexedEtaCompute.computeWeakening (heq : env.HasCanonicalEq) :
    ∀ stage, ComputeWeakening (TypedIndexedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact fun W R => R.weakN (fun W H => KCertificate.weakN W H) W
  | succ stage ih => exact fun W R => R.weakN (TypedIndexedNext.weakens heq ih) W

/-- The preceding stage is included among the next ordinary steps. -/
theorem TypedIndexedEtaCompute.next (R : TypedIndexedEtaCompute D kdepth stage Γ e out) :
    TypedIndexedEtaCompute D kdepth (stage + 1) Γ e out := .base (.inl (.inl (.inl R)))

/-- Finitely many stage bounds can be combined. -/
theorem TypedIndexedEtaCompute.mono (hle : stage ≤ stage')
    (R : TypedIndexedEtaCompute D kdepth stage Γ e out) :
    TypedIndexedEtaCompute D kdepth stage' Γ e out := by
  induction hle with
  | refl => exact R
  | step _ ih => exact ih.next

/-- All previously checked indexed stages embed at the same bound. No claim
of strict enlargement over their finite union is made. -/
theorem TypedIndexedEtaCompute.of_indexed :
    ∀ stage, ∀ {Γ e out}, IndexedEtaCompute D kdepth stage Γ e out →
      TypedIndexedEtaCompute D kdepth stage Γ e out := by
  intro stage
  induction stage with
  | zero => exact fun R => R
  | succ stage ih =>
    intro Γ e out R
    exact RecoveredEtaWith.mono (fun H => .inl (IndexedNextComputation.mono ih H)) R

/-- Type-restricted recovery supplies an ordinary eta step at the next stage. -/
theorem TypedIndexedEtaCompute.eta_from_types
    (R : TypeRecoveryWith (TypeHeadExtension (TypedIndexedEtaCompute D kdepth stage))
      Γ e (.forallE A B)) :
    TypedIndexedEtaCompute D kdepth (stage + 1) Γ e (.lam A (.app e.lift (.bvar 0))) :=
  .base (.inr (.inr (.inr (.eta R))))

/-- An inferred outer cast can be removed for eta annotation recovery using
payload head computation alone. Endpoint comparison is not an extra premise. -/
theorem TypedIndexedEtaCompute.eta_from_cast
    (R : TypeRecoveryWith (TypedIndexedEtaCompute D kdepth stage) Γ e (typeCast u X Y p x))
    (H : TypedIndexedEtaCompute D kdepth stage Γ x (.forallE A B)) :
    TypedIndexedEtaCompute D kdepth (stage + 1) Γ e (.lam A (.app e.lift (.bvar 0))) :=
  eta_from_types (.convert (R.mono (fun H => .base H)) (.castPi H))

/-- Recovered comparisons using cast-head types guard arbitrary indexed
singleton programs while retaining their exact generated target. -/
theorem TypedIndexedEtaCompute.prefix_from_types
    (R : GuardedSingleton.PrefixStep
      (RecoveredComparisonWith (TypeHeadExtension (TypedIndexedEtaCompute D kdepth stage)) true)
      Γ e out) : TypedIndexedEtaCompute D kdepth (stage + 1) Γ e out :=
  .base (.inr (.inr (.inl R)))

/-- The same recovered endpoint comparisons guard a general Eq.rec K step. -/
theorem TypedIndexedEtaCompute.eqRec_from_types
    (H : RecoveredComparisonWith (TypeHeadExtension (TypedIndexedEtaCompute D kdepth stage))
      true Γ a b) :
    TypedIndexedEtaCompute D kdepth (stage + 1) Γ (eqRecApp v w α a M m b p) m :=
  .base (.inr (.inl (.eqRec H)))

/-- Identity insertion replays each stage at any supplied source type. -/
theorem TypedIndexedEtaCompute.simAt (R : TypedIndexedEtaCompute D kdepth stage Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  ComputeDescent.simAt (computeDescent heq hs stage) R hΓ

end Lean4Lean.VEnv.Strengthening
