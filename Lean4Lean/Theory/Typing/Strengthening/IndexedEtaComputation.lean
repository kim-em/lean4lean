import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonWeakening

/-! # Finite recovery stages with arbitrary indexed singleton prefixes

Both K and the registered prefix generator may use endpoint comparisons from
the preceding stage. Compatible computation and recovered eta then close the
new stage. No completeness of family certificates is assumed or asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
variable {C C' : List VExpr → VExpr → VExpr → Prop}

/-- Predecessor computations, guarded K, and generated indexed prefixes. -/
def IndexedNextComputation (D : Definitions) (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (e out : VExpr) : Prop :=
  ComparedNextComputation D C Γ e out ∨
    GuardedSingleton.PrefixStep (RecoveryComparisonGuard C) Γ e out

/-- Both exceptional rules discharge their comparisons at the previous stage. -/
theorem IndexedNextComputation.descends (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) :
    ComputeDescent (IndexedNextComputation D C) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  exact R.elim
    (fun R => ComparedNextComputation.descends heq hs hc R W hΓ hΓ' ht)
    (fun R => GuardedSingleton.PrefixStep.computeDescent heq
      (RecoveryComparisonGuard.descends hc) R W hΓ hΓ' ht)

/-- Raw prefix guards survive insertion before source typing is recovered. -/
theorem IndexedNextComputation.weakens (heq : env.HasCanonicalEq)
    (hw : ComputeWeakening C) : ComputeWeakening (IndexedNextComputation D C) := by
  intro n k Γ Γ' e out W R
  exact R.elim
    (fun R => .inl (ComparedNextComputation.weakens hw W R))
    (fun R => .inr (GuardedSingleton.PrefixStep.computeWeakening heq
      (fun W H => H.weakN hw W) W R))

/-- Increasing the preceding computation relation preserves every guard. -/
theorem IndexedNextComputation.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (R : IndexedNextComputation D C Γ e out) : IndexedNextComputation D C' Γ e out := by
  have hguard : ∀ {Γ a b}, RecoveryComparisonGuard C Γ a b →
      RecoveryComparisonGuard C' Γ a b :=
    fun H => H.elim (fun H => .inl (H.mono hC)) (fun H => .inr (H.mono hC))
  exact R.elim
    (fun R => .inl (R.elim (fun R => .inl (hC R)) (fun R => .inr (R.map_guards hguard))))
    (fun R => .inr (R.map_guards hguard))

/-- Every new guard and recovered eta type has a finite predecessor stage. -/
def IndexedEtaCompute (D : Definitions) (kdepth : Nat) :
    Nat → List VExpr → VExpr → VExpr → Prop
  | 0 => CertifiedKCompute D kdepth
  | stage + 1 => RecoveredEtaWith (IndexedNextComputation D (IndexedEtaCompute D kdepth stage))

/-- Every finite indexed stage reflects scope and replays at the source type. -/
theorem IndexedEtaCompute.computeDescent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ∀ stage, ComputeDescent (IndexedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact CertifiedKCompute.computeDescent heq hs
  | succ stage ih =>
    exact RecoveredEtaWith.computeDescent (IndexedNextComputation.descends heq hs ih)

/-- Every finite indexed stage is stable beneath inserted binders. -/
theorem IndexedEtaCompute.computeWeakening (heq : env.HasCanonicalEq) :
    ∀ stage, ComputeWeakening (IndexedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact fun W R => R.weakN (fun W H => KCertificate.weakN W H) W
  | succ stage ih => exact fun W R => R.weakN (IndexedNextComputation.weakens heq ih) W

/-- Earlier stages embed without changing the output term. -/
theorem IndexedEtaCompute.next (R : IndexedEtaCompute D kdepth stage Γ e out) :
    IndexedEtaCompute D kdepth (stage + 1) Γ e out := .base (.inl (.inl R))

/-- Finitely many certificates can be raised to one common stage. -/
theorem IndexedEtaCompute.mono (hle : stage ≤ stage')
    (R : IndexedEtaCompute D kdepth stage Γ e out) :
    IndexedEtaCompute D kdepth stage' Γ e out := by
  induction hle with
  | refl => exact R
  | step _ ih => exact ih.next

/-- All previous recovered-comparison stages remain available at the same bound. -/
theorem IndexedEtaCompute.of_compared :
    ∀ stage, ∀ {Γ e out}, ComparedEtaCompute D kdepth stage Γ e out →
      IndexedEtaCompute D kdepth stage Γ e out := by
  intro stage
  induction stage with
  | zero => exact fun R => R
  | succ stage ih =>
    intro Γ e out R
    refine RecoveredEtaWith.mono ?_ R
    intro Γ e out R
    exact .inl (R.elim (fun R => .inl (ih R))
      (fun R => .inr (R.map_guards (fun H => H.elim
        (fun H => .inl (H.mono ih)) (fun H => .inr (H.mono ih))))))

/-- A guarded arbitrary indexed prefix enters the next compatible stage. -/
theorem IndexedEtaCompute.prefix
    (R : GuardedSingleton.PrefixStep (RecoveryComparisonGuard
      (IndexedEtaCompute D kdepth stage)) Γ e out) :
    IndexedEtaCompute D kdepth (stage + 1) Γ e out := .base (.inr R)

/-- Types recovered at a finite indexed stage can annotate the next eta step. -/
theorem IndexedEtaCompute.eta
    (R : TypeRecoveryWith (IndexedEtaCompute D kdepth stage) Γ e (.forallE A B)) :
    IndexedEtaCompute D kdepth (stage + 1) Γ e (.lam A (.app e.lift (.bvar 0))) :=
  RecoveredEtaWith.eta (R.mono (fun H => Or.inl (Or.inl H)))

/-- Direct recovered endpoint comparisons also guard K in the new model. -/
theorem IndexedEtaCompute.eqRec_recovered
    (H : RecoveredComparisonWith (IndexedEtaCompute D kdepth stage) true Γ a b) :
    IndexedEtaCompute D kdepth (stage + 1) Γ (eqRecApp v w α a M m b p) m := by
  have hr : ∀ e, IndexedEtaCompute D kdepth stage Γ e e :=
    fun e => of_compared stage (ComparedEtaCompute.of_staged stage StagedEtaCompute.refl)
  exact .base (.inl (.inr (.eqRec (.inr ⟨a, b, hr a, hr b, H⟩))))

/-- Replay follows from descent along the identity context insertion. -/
theorem IndexedEtaCompute.simAt (R : IndexedEtaCompute D kdepth stage Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  ComputeDescent.simAt (computeDescent heq hs stage) R hΓ

end Lean4Lean.VEnv.Strengthening
