import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaComputation

/-! # Finite interaction between recovered eta, type computation and K

Every stage may recover eta annotations using the preceding stage's computation.
It may also contract K when preceding-stage computations align the endpoints.
The recursion is on certificates, not reduction length or term normalization.
Every finite stage has typed descent. Full-conversion coverage is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Endpoints compute to a hybrid normal comparison using the chosen base. -/
def ComputedComparison (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b' n, C Γ a a' ∧ C Γ b b' ∧ HybridNormal n Γ a' b'

/-- Typed endpoint descent follows from base descent and hybrid normal descent. -/
theorem ComputedComparison.descends (hc : ComputeDescent C) :
    EndpointDescent (ComputedComparison C) := by
  intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
  obtain ⟨a', b', n, Ra, Rb, H⟩ := H
  obtain ⟨a₀, rfl, Ea⟩ := hc Ra W hΓ hΓ' ha
  obtain ⟨b₀, rfl, Eb⟩ := hc Rb W hΓ hΓ' hb
  obtain ⟨u, hα⟩ := ha.isType henv hΓ
  have E := (HybridNormal.descend n W hΓ hΓ' Ea.hasType.2 Eb.hasType.2 H).1 ⟨_, hα⟩
  exact ⟨_, Ea.trans ((E.of_l henv hΓ Ea.hasType.2).trans Eb.symm)⟩

/-- Weakening preserves the computations and the final comparison. -/
theorem ComputedComparison.weakN (hc : ComputeWeakening C)
    (W : Ctx.LiftN n k Γ Γ') (H : ComputedComparison C Γ a b) :
    ComputedComparison C Γ' (a.liftN n k) (b.liftN n k) := by
  obtain ⟨a', b', i, Ra, Rb, H⟩ := H
  exact ⟨_, _, i, hc W Ra, hc W Rb, H.weakN W⟩

/-- A stage can use the preceding computation or K guarded by its computed
comparisons. The surrounding eta closure supplies compatibility and composition. -/
def NextComputation (D : Definitions) (C : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  C Γ a b ∨ GuardedKCompute D (ComputedComparison C) Γ a b

/-- Both alternatives have checked source-typed descent. -/
theorem NextComputation.descends (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : ComputeDescent C) : ComputeDescent (NextComputation D C) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  cases R with
  | inl R => exact hc R W hΓ hΓ' ht
  | inr R =>
    obtain ⟨out, hout, H⟩ := R.descend heq hs (ComputedComparison.descends hc) W hΓ hΓ'
    exact ⟨out, hout, H _ ht⟩

/-- The stage base weakens whenever its preceding computation does. -/
theorem NextComputation.weakens (hc : ComputeWeakening C) :
    ComputeWeakening (NextComputation D C) := by
  intro n k Γ Γ' e out W R
  cases R with
  | inl R => exact .inl (hc W R)
  | inr R => exact .inr (R.weakN (fun W H => H.weakN hc W) W)

/-- Depth counts finite interactions of recovered eta and K. The independent
`kdepth` parameter retains all previously certified nested K computations. -/
def StagedEtaCompute (D : Definitions) (kdepth : Nat) :
    Nat → List VExpr → VExpr → VExpr → Prop
  | 0 => CertifiedKCompute D kdepth
  | stage + 1 => RecoveredEtaWith (NextComputation D (StagedEtaCompute D kdepth stage))

/-- No new descent assumption is needed at any finite stage. -/
theorem StagedEtaCompute.computeDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ComputeDescent (StagedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact CertifiedKCompute.computeDescent heq hs
  | succ stage ih => exact RecoveredEtaWith.computeDescent (NextComputation.descends heq hs ih)

/-- Stages preserve finite binder insertion, including every nested recovery. -/
theorem StagedEtaCompute.computeWeakening :
    ∀ stage, ComputeWeakening (StagedEtaCompute D kdepth stage) := by
  intro stage
  induction stage with
  | zero => exact fun W R => R.weakN (fun W H => KCertificate.weakN W H) W
  | succ stage ih => exact fun W R => R.weakN (NextComputation.weakens ih) W


/-- A staged computation weakens without changing either depth bound. -/
theorem StagedEtaCompute.weakN (W : Ctx.LiftN n k Γ Γ')
    (R : StagedEtaCompute D kdepth stage Γ e out) :
    StagedEtaCompute D kdepth stage Γ' (e.liftN n k) (out.liftN n k) :=
  computeWeakening stage W R

/-- Earlier computations remain available at the next stage. -/
theorem StagedEtaCompute.next (R : StagedEtaCompute D kdepth stage Γ e out) :
    StagedEtaCompute D kdepth (stage + 1) Γ e out := .base (.inl R)

/-- Stages are monotone, so finitely many certificates can share one stage. -/
theorem StagedEtaCompute.mono (hle : stage ≤ stage')
    (R : StagedEtaCompute D kdepth stage Γ e out) :
    StagedEtaCompute D kdepth stage' Γ e out := by
  induction hle with
  | refl => exact R
  | step _ ih => exact ih.next

/-- Every stage includes identity computation. -/
theorem StagedEtaCompute.refl : StagedEtaCompute D kdepth stage Γ e e := by
  induction stage with
  | zero => exact .base .refl
  | succ stage ih => exact ih.next

/-- The original eta computation is included at stage one. -/
theorem StagedEtaCompute.ofRecovered (R : RecoveredEtaCompute D kdepth Γ e out) :
    StagedEtaCompute D kdepth 1 Γ e out := R.mono (fun H => Or.inl H)

/-- Typed lifted sources reconstruct their exact output and equality below. -/
theorem StagedEtaCompute.descend
    (R : StagedEtaCompute D kdepth stage Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out T :=
  computeDescent heq hs stage R W hΓ hΓ' ht

/-- Ordinary typed replay at every stage. -/
theorem StagedEtaCompute.simAt (R : StagedEtaCompute D kdepth stage Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  ComputeDescent.simAt (computeDescent heq hs stage) R hΓ

/-- A chosen type may now compute using preceding eta and K interactions. -/
abbrev StagedTypeRecovery (D : Definitions) (kdepth stage : Nat) :=
  TypeRecoveryWith (StagedEtaCompute D kdepth stage)


/-- The whole chosen type is reconstructed below at every finite stage. -/
theorem StagedTypeRecovery.descend
    (R : StagedTypeRecovery D kdepth stage Γ' (e.lift' ρ) T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ T₀, T = T₀.lift' ρ ∧ env.HasType univs Γ e T₀ :=
  TypeRecoveryWith.descend R (StagedEtaCompute.computeDescent heq hs stage) W hΓ hΓ' ht

/-- Recovery is sound from source well-formedness at every finite stage. -/
theorem StagedTypeRecovery.hasType (R : StagedTypeRecovery D kdepth stage Γ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    env.HasType univs Γ e T :=
  TypeRecoveryWith.hasType R (StagedEtaCompute.computeDescent heq hs stage) hΓ ht

/-- Recovery survives binder insertion at the same stage. -/
theorem StagedTypeRecovery.weakN (W : Ctx.LiftN n k Γ Γ')
    (R : StagedTypeRecovery D kdepth stage Γ e T) :
    StagedTypeRecovery D kdepth stage Γ' (e.liftN n k) (T.liftN n k) :=
  TypeRecoveryWith.weakN (StagedEtaCompute.computeWeakening stage) W R

/-- A recovered Pi may drive eta at the next stage, including when its recovery
already used eta-dependent K computations inside the type. -/
theorem StagedEtaCompute.eta (R : StagedTypeRecovery D kdepth stage Γ e (.forallE A B)) :
    StagedEtaCompute D kdepth (stage + 1) Γ e (.lam A (.app e.lift (.bvar 0))) :=
  RecoveredEtaWith.eta (R.mono (fun H => Or.inl H))

/-- K may use endpoints aligned by any preceding stage. -/
theorem StagedEtaCompute.eqRec (H : ComputedComparison (StagedEtaCompute D kdepth stage) Γ a b) :
    StagedEtaCompute D kdepth (stage + 1) Γ (eqRecApp v w α a M m b p) m :=
  .base (.inr (.eqRec H))

/-- A single computation supplies a comparison with its typed endpoint. -/
theorem StagedEtaCompute.comparison (R : StagedEtaCompute D kdepth stage Γ a b)
    (hb : env.HasType univs Γ b T) : ComputedComparison (StagedEtaCompute D kdepth stage) Γ a b :=
  ⟨b, b, 0, R, .refl, .refl hb⟩

end Lean4Lean.VEnv.Strengthening
