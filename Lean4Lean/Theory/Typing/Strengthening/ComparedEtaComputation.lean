import Lean4Lean.Theory.Typing.Strengthening.StagedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparisonCore

/-! # K guards with recovered application comparisons

After computing the endpoints, a K guard may compare them using recovered
types at application nodes. Both endpoint computation and type recovery use
the preceding stage, so descent remains a finite induction. Existing hybrid
guards are retained. General equality coverage is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
variable {C C' : List VExpr → VExpr → VExpr → Prop}

/-- Computed endpoints may use recovered types in their final comparison. -/
def RecoveredComputedComparison (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b', C Γ a a' ∧ C Γ b b' ∧ RecoveredComparisonWith C true Γ a' b'

/-- Reconstruct both computed endpoints at their common source type, then use
the generic recovered-comparison descent theorem. -/
theorem RecoveredComputedComparison.descends (hc : ComputeDescent C) :
    EndpointDescent (RecoveredComputedComparison C) := by
  intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
  obtain ⟨a', b', Ra, Rb, H⟩ := H
  obtain ⟨a₀, rfl, Ea⟩ := hc Ra W hΓ hΓ' ha
  obtain ⟨b₀, rfl, Eb⟩ := hc Rb W hΓ hΓ' hb
  obtain ⟨u, hα⟩ := ha.isType henv hΓ
  have E := H.descend hc W hΓ hΓ' Ea.hasType.2 Eb.hasType.2 ⟨_, hα⟩
  exact ⟨_, Ea.trans ((E.of_l henv hΓ Ea.hasType.2).trans Eb.symm)⟩

/-- Computations and recovered endpoint types weaken together. -/
theorem RecoveredComputedComparison.weakN (hw : ComputeWeakening C)
    (W : Ctx.LiftN n k Γ Γ') (H : RecoveredComputedComparison C Γ a b) :
    RecoveredComputedComparison C Γ' (a.liftN n k) (b.liftN n k) := by
  obtain ⟨a', b', Ra, Rb, H⟩ := H
  exact ⟨_, _, hw W Ra, hw W Rb, H.weakN hw W⟩

/-- Enlarging computation also enlarges recovery inside endpoint comparison. -/
theorem RecoveredComputedComparison.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (H : RecoveredComputedComparison C Γ a b) : RecoveredComputedComparison C' Γ a b := by
  obtain ⟨a', b', Ra, Rb, H⟩ := H
  exact ⟨a', b', hC Ra, hC Rb, H.mono hC⟩

/-- The original hybrid comparison is monotone in its computations as well. -/
theorem ComputedComparison.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (H : ComputedComparison C Γ a b) : ComputedComparison C' Γ a b := by
  obtain ⟨a', b', n, Ra, Rb, H⟩ := H
  exact ⟨a', b', n, hC Ra, hC Rb, H⟩

/-- Compatible K paths can replace every endpoint guard with an enlarged one. -/
theorem GuardedKCompute.map_guards
    (hCmp : ∀ {Γ a b}, Cmp Γ a b → Cmp' Γ a b)
    (R : GuardedKCompute D Cmp Γ e out) : GuardedKCompute D Cmp' Γ e out := by
  induction R with
  | base R => exact .base R
  | eqRec H => exact .eqRec (hCmp H)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Keep hybrid guards and admit the recovered application comparison. -/
def RecoveryComparisonGuard (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ComputedComparison C Γ a b ∨ RecoveredComputedComparison C Γ a b

/-- Both alternatives have checked common-type endpoint descent. -/
theorem RecoveryComparisonGuard.descends (hc : ComputeDescent C) :
    EndpointDescent (RecoveryComparisonGuard C) := by
  intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
  exact H.elim (fun H => ComputedComparison.descends hc W hΓ hΓ' ha hb H)
    (fun H => RecoveredComputedComparison.descends hc W hΓ hΓ' ha hb H)

/-- Both guard alternatives preserve finite binder insertion. -/
theorem RecoveryComparisonGuard.weakN (hw : ComputeWeakening C)
    (W : Ctx.LiftN n k Γ Γ') (H : RecoveryComparisonGuard C Γ a b) :
    RecoveryComparisonGuard C Γ' (a.liftN n k) (b.liftN n k) :=
  H.elim (fun H => .inl (H.weakN hw W)) (fun H => .inr (H.weakN hw W))

/-- The computation at the next stage may use either kind of K guard. -/
def ComparedNextComputation (D : Definitions) (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (e out : VExpr) : Prop :=
  C Γ e out ∨ GuardedKCompute D (RecoveryComparisonGuard C) Γ e out

/-- Recovery-aware guards supply all descent hypotheses needed by K. -/
theorem ComparedNextComputation.descends (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) :
    ComputeDescent (ComparedNextComputation D C) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  cases R with
  | inl R => exact hc R W hΓ hΓ' ht
  | inr R =>
    obtain ⟨out, hout, H⟩ := R.descend heq hs (RecoveryComparisonGuard.descends hc) W hΓ hΓ'
    exact ⟨out, hout, H _ ht⟩

/-- Weakening transforms each K guard and each recovered type. -/
theorem ComparedNextComputation.weakens (hw : ComputeWeakening C) :
    ComputeWeakening (ComparedNextComputation D C) := by
  intro n k Γ Γ' e out W R
  exact R.elim (fun R => .inl (hw W R))
    (fun R => .inr (R.weakN (fun W H => H.weakN hw W) W))

/-- Each stage's comparisons and eta recoveries use only its predecessor. -/
def ComparedEtaCompute (D : Definitions) (kdepth : Nat) :
    Nat → List VExpr → VExpr → VExpr → Prop
  | 0 => CertifiedKCompute D kdepth
  | stage + 1 => RecoveredEtaWith (ComparedNextComputation D (ComparedEtaCompute D kdepth stage))

/-- Every finite stage descends, with no equality-completeness premise. -/
theorem ComparedEtaCompute.computeDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ComputeDescent (ComparedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact CertifiedKCompute.computeDescent heq hs
  | succ stage ih => exact RecoveredEtaWith.computeDescent (ComparedNextComputation.descends heq hs ih)

/-- Every finite stage weakens without increasing its bound. -/
theorem ComparedEtaCompute.computeWeakening :
    ∀ stage, ComputeWeakening (ComparedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact fun W R => R.weakN (fun W H => KCertificate.weakN W H) W
  | succ stage ih => exact fun W R => R.weakN (ComparedNextComputation.weakens ih) W

/-- Earlier certificates remain available in the next stage. -/
theorem ComparedEtaCompute.next (R : ComparedEtaCompute D kdepth stage Γ e out) :
    ComparedEtaCompute D kdepth (stage + 1) Γ e out := .base (.inl R)

/-- A finite collection of comparison/recovery stages can share a larger bound. -/
theorem ComparedEtaCompute.mono (hle : stage ≤ stage')
    (R : ComparedEtaCompute D kdepth stage Γ e out) :
    ComparedEtaCompute D kdepth stage' Γ e out := by
  induction hle with
  | refl => exact R
  | step _ ih => exact ih.next

/-- The earlier staged model embeds at exactly the same stage. This inclusion
does not assert that the new guard is strictly stronger than its finite union. -/
theorem ComparedEtaCompute.of_staged :
    ∀ stage, ∀ {Γ e out}, StagedEtaCompute D kdepth stage Γ e out →
      ComparedEtaCompute D kdepth stage Γ e out := by
  intro stage
  induction stage with
  | zero => exact fun R => R
  | succ stage ih =>
    intro Γ e out R
    refine RecoveredEtaWith.mono ?_ R
    intro Γ e out R
    exact R.elim (fun R => .inl (ih R))
      (fun R => .inr (R.map_guards (fun H => .inl (H.mono ih))))

/-- A direct recovered comparison is a computed guard using reflexive paths. -/
theorem ComparedEtaCompute.eqRec_recovered
    (H : RecoveredComparisonWith (ComparedEtaCompute D kdepth stage) true Γ a b) :
    ComparedEtaCompute D kdepth (stage + 1) Γ (eqRecApp v w α a M m b p) m := by
  have hr : ∀ e, ComparedEtaCompute D kdepth stage Γ e e :=
    fun e => of_staged stage StagedEtaCompute.refl
  exact .base (.inr (.eqRec (.inr ⟨a, b, hr a, hr b, H⟩)))

/-- Types recovered by the preceding stage supply the next eta annotation. -/
theorem ComparedEtaCompute.eta
    (R : TypeRecoveryWith (ComparedEtaCompute D kdepth stage) Γ e (.forallE A B)) :
    ComparedEtaCompute D kdepth (stage + 1) Γ e (.lam A (.app e.lift (.bvar 0))) :=
  RecoveredEtaWith.eta (R.mono (fun H => Or.inl H))

/-- The identity context insertion gives typed replay at the source type. -/
theorem ComparedEtaCompute.simAt (R : ComparedEtaCompute D kdepth stage Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  ComputeDescent.simAt (computeDescent heq hs stage) R hΓ

end Lean4Lean.VEnv.Strengthening
