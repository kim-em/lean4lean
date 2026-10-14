import Lean4Lean.Theory.Typing.Strengthening.FamilyRecoveryExistence
import Lean4Lean.Theory.Typing.Strengthening.StagedRecoverySubstitution

/-! # Recovery with a certificate-dependent finite stage

Head exposure need not have one uniform stage bound. A recovery using finitely
many computations from the union of stages can always be collected into one
stage. This preserves checked descent and gives a precise nonuniform version
of the still-open head-exposure obligations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Each computation may choose its own finite interaction depth. The bound
on the original K certificates remains the fixed parameter `kdepth`. -/
def FiniteStagedCompute (D : Definitions) (kdepth : Nat)
    (Γ : List VExpr) (e out : VExpr) : Prop :=
  ∃ stage, StagedEtaCompute D kdepth stage Γ e out

/-- Existential stage choice retains exact scope reflection and typed replay. -/
theorem FiniteStagedCompute.computeDescent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ComputeDescent (FiniteStagedCompute D kdepth) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  obtain ⟨stage, R⟩ := R
  exact R.descend heq hs W hΓ hΓ' ht

/-- Weakening keeps the witness stage. -/
theorem FiniteStagedCompute.computeWeakening :
    ComputeWeakening (FiniteStagedCompute D kdepth) := by
  intro n k Γ Γ' e out W R
  obtain ⟨stage, R⟩ := R
  exact ⟨stage, R.weakN W⟩

/-- A fixed-stage recovery is also a recovery over the union. -/
theorem StagedTypeRecovery.toFinite (R : StagedTypeRecovery D kdepth stage Γ e T) :
    TypeRecoveryWith (FiniteStagedCompute D kdepth) Γ e T :=
  R.mono (fun H => ⟨stage, H⟩)

/-- Finite certificates use only finitely many stages. Conversion takes the
maximum of its input-recovery and computation stages; the other constructors
retain the stage of their sole recovery premise. -/
theorem TypeRecoveryWith.finite_stage
    (R : TypeRecoveryWith (FiniteStagedCompute D kdepth) Γ e T) :
    ∃ stage, StagedTypeRecovery D kdepth stage Γ e T := by
  induction R with
  | sort h => exact ⟨0, .sort h⟩
  | const hc hw hl => exact ⟨0, .const hc hw hl⟩
  | bvar h => exact ⟨0, .bvar h⟩
  | lam _ ih =>
    obtain ⟨stage, R⟩ := ih
    exact ⟨stage, .lam R⟩
  | app _ ih =>
    obtain ⟨stage, R⟩ := ih
    exact ⟨stage, .app R⟩
  | forallE hA hB => exact ⟨0, .forallE hA hB⟩
  | proj hi _ hF ih =>
    obtain ⟨stage, R⟩ := ih
    exact ⟨stage, .proj hi R hF⟩
  | convert _ H ih =>
    obtain ⟨n, R⟩ := ih
    obtain ⟨m, H⟩ := H
    exact ⟨max n m, .convert (R.mono (fun R => R.mono (Nat.le_max_left n m)))
      (H.mono (Nat.le_max_right n m))⟩

/-- Taking the union inside recovery adds no infinite certificates. -/
theorem finite_recovery_iff :
    TypeRecoveryWith (FiniteStagedCompute D kdepth) Γ e T ↔
      ∃ stage, StagedTypeRecovery D kdepth stage Γ e T :=
  ⟨TypeRecoveryWith.finite_stage, fun ⟨_, R⟩ => R.toFinite⟩

/-- Two finite paths compose at their maximum stage. -/
theorem FiniteStagedCompute.trans
    (R : FiniteStagedCompute D kdepth Γ a b)
    (S : FiniteStagedCompute D kdepth Γ b c) :
    FiniteStagedCompute D kdepth Γ a c := by
  obtain ⟨n, R⟩ := R
  obtain ⟨m, S⟩ := S
  exact ⟨max n m, (R.mono (Nat.le_max_left n m)).trans
    (S.mono (Nat.le_max_right n m))⟩

/-- Recovery over the union drives eta within the same union. This does not
require a global stage bound on all recoveries. -/
theorem FiniteStagedCompute.eta
    (R : TypeRecoveryWith (FiniteStagedCompute D kdepth) Γ e (.forallE A B)) :
    FiniteStagedCompute D kdepth Γ e (.lam A (.app e.lift (.bvar 0))) := by
  obtain ⟨stage, R⟩ := R.finite_stage
  exact ⟨stage + 1, StagedEtaCompute.eta R⟩

/-- A K guard whose endpoint computations choose different finite stages can
be collected at their maximum, then used by the next stage. -/
theorem FiniteStagedCompute.eqRec
    (H : ComputedComparison (FiniteStagedCompute D kdepth) Γ a b) :
    FiniteStagedCompute D kdepth Γ (eqRecApp v w α a M m b p) m := by
  obtain ⟨a', b', i, ⟨n, Ra⟩, ⟨r, Rb⟩, H⟩ := H
  exact ⟨max n r + 1, StagedEtaCompute.eqRec
    ⟨a', b', i, Ra.mono (Nat.le_max_left n r), Rb.mono (Nat.le_max_right n r), H⟩⟩

/-- Application compatibility combines independently chosen stages. -/
theorem FiniteStagedCompute.app
    (R : FiniteStagedCompute D kdepth Γ f f')
    (S : FiniteStagedCompute D kdepth Γ a a') :
    FiniteStagedCompute D kdepth Γ (.app f a) (.app f' a') := by
  obtain ⟨n, R⟩ := R
  obtain ⟨m, S⟩ := S
  exact ⟨max n m + 1, .app (R.mono (Nat.le_max_left n m)).next
    (S.mono (Nat.le_max_right n m)).next⟩

/-- Lambda compatibility retains the source-domain context for the body. -/
theorem FiniteStagedCompute.lam
    (R : FiniteStagedCompute D kdepth Γ A A')
    (S : FiniteStagedCompute D kdepth (A :: Γ) b b') :
    FiniteStagedCompute D kdepth Γ (.lam A b) (.lam A' b') := by
  obtain ⟨n, R⟩ := R
  obtain ⟨m, S⟩ := S
  exact ⟨max n m + 1, .lam (R.mono (Nat.le_max_left n m)).next
    (S.mono (Nat.le_max_right n m)).next⟩

/-- Pi compatibility likewise uses the source-domain context. -/
theorem FiniteStagedCompute.forallE
    (R : FiniteStagedCompute D kdepth Γ A A')
    (S : FiniteStagedCompute D kdepth (A :: Γ) B B') :
    FiniteStagedCompute D kdepth Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨n, R⟩ := R
  obtain ⟨m, S⟩ := S
  exact ⟨max n m + 1, .forallE (R.mono (Nat.le_max_left n m)).next
    (S.mono (Nat.le_max_right n m)).next⟩

/-- Projection compatibility keeps a finite stage. -/
theorem FiniteStagedCompute.proj
    (R : FiniteStagedCompute D kdepth Γ m m') :
    FiniteStagedCompute D kdepth Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨n, R⟩ := R
  exact ⟨n + 1, .proj R.next⟩

/-- All compatible K paths guarded by finite computations already belong to
the finite union. There is no additional closure gap at this layer. -/
theorem FiniteStagedCompute.of_guarded
    (R : GuardedKCompute D (ComputedComparison (FiniteStagedCompute D kdepth)) Γ e out) :
    FiniteStagedCompute D kdepth Γ e out := by
  induction R with
  | base R => exact ⟨0, .base R⟩
  | eqRec H => exact eqRec H
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ ih1 ih2 => exact ih1.lam ih2
  | forallE _ _ ih1 ih2 => exact ih1.forallE ih2
  | proj _ ih => exact ih.proj

/-- The next computational base adds nothing to the finite union. -/
theorem FiniteStagedCompute.of_next
    (R : NextComputation D (FiniteStagedCompute D kdepth) Γ e out) :
    FiniteStagedCompute D kdepth Γ e out :=
  R.elim id of_guarded

/-- The finite union is a fixed point of the complete eta/K stage operation.
Thus further finite alternation cannot supply a new computational capability;
coverage of arbitrary equality is a separate, still-open issue. -/
theorem finite_staged_fixedPoint :
    RecoveredEtaWith (NextComputation D (FiniteStagedCompute D kdepth)) Γ e out ↔
      FiniteStagedCompute D kdepth Γ e out := by
  constructor
  · intro R
    induction R with
    | base R => exact FiniteStagedCompute.of_next R
    | eta R => exact FiniteStagedCompute.eta (R.mono FiniteStagedCompute.of_next)
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
    | app _ _ ih1 ih2 => exact ih1.app ih2
    | lam _ _ ih1 ih2 => exact ih1.lam ih2
    | forallE _ _ ih1 ih2 => exact ih1.forallE ih2
    | proj _ ih => exact ih.proj
  · exact fun R => .base (.inl R)

/-- Nonuniform Pi and family exposure suffice for recovery at some finite
stage. The exposure premises remain open; no uniform stage is asserted. -/
theorem finite_recovery_of_head_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hPi : RecoveryPiExposure (FiniteStagedCompute D kdepth))
    (hFamily : RecoveryFamilyExposure (FiniteStagedCompute D kdepth))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ stage T, StagedTypeRecovery D kdepth stage Γ e T := by
  obtain ⟨T, R⟩ := RecoveryExists.of_head_exposure
    (FiniteStagedCompute.computeDescent heq hs) hPi hFamily hΓ ht
  obtain ⟨stage, R⟩ := R.finite_stage
  exact ⟨stage, T, R⟩

/-- Under those same unproved head clauses, arbitrary typed substitution
re-synthesizes a finite-stage output convertible to the old substituted type.
The argument need not recover its declared type, and the new stage may grow. -/
theorem StagedTypeRecovery.resynthesize_finite_instN
    (R : StagedTypeRecovery D kdepth stage Γ₁ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hPi : RecoveryPiExposure (FiniteStagedCompute D kdepth))
    (hFamily : RecoveryFamilyExposure (FiniteStagedCompute D kdepth))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    ∃ stage' T', StagedTypeRecovery D kdepth stage' Γ (e.inst x k) T' ∧
      env.IsDefEqU univs Γ (T.inst x k) T' := by
  have hc : ComputeDescent (FiniteStagedCompute D kdepth) :=
    FiniteStagedCompute.computeDescent heq hs
  have H := RecoveryHeads.of_type_exposure hc hPi (hFamily.projectionExposure hc)
  obtain ⟨T', R', hT⟩ := R.toFinite.resynthesize_instN hc H hΓ₁ hx W ht
  obtain ⟨stage', R'⟩ := R'.finite_stage
  exact ⟨stage', T', R', hT⟩

end Lean4Lean.VEnv.Strengthening
