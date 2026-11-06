import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertIdentityFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants

/-! # Constant deletion through typed mixed continuation frames

Track a removed constant wrapper through function positions, retained lambda
bodies and identity payloads. Actual source typing supplies the lower payload
needed to descend computation below the unused binder. Simulation changes endpoints, keeps each guarded
computation in its original scope, and never increases its primitive count.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta

/-- Delete one constant wrapper at a tracked head position, or retain equality
after it has been consumed. The relation is raw; simulation of guarded paths
will require typing of their actual sources. -/
inductive ConstantHeadDeletion : ProofShape → ProofShape → Prop where
  | refl : ConstantHeadDeletion e e
  | drop : ConstantHeadDeletion (.app (.lam A (e.liftN 1)) x) e
  | app : ConstantHeadDeletion f f' → ConstantHeadDeletion (.app f a) (.app f' a)
  | lam : ConstantHeadDeletion b b' → ConstantHeadDeletion (.lam A b) (.lam A b')
  | identity : ConstantHeadDeletion e e' →
      ConstantHeadDeletion (.app (.lam A (.bvar 0)) e) (.app (.lam A (.bvar 0)) e')

/-- Pending arguments preserve the tracked deletion. -/
theorem ConstantHeadDeletion.mkApps (H : ConstantHeadDeletion f f') (args : List ProofShape) :
    ConstantHeadDeletion (ProofShape.mkApps f args) (ProofShape.mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact H
  | cons a args ih => exact ih (.app H)

/-- Raw endpoint substitution preserves the tracked deletion without any
substitution principle for primitive guards. -/
theorem ConstantHeadDeletion.subst (H : ConstantHeadDeletion e e') (τ : ProofShape.Subst) :
    ConstantHeadDeletion (e.subst τ) (e'.subst τ) := by
  induction H generalizing τ with
  | refl => exact .refl
  | @drop A x e => simpa only [ProofShape.subst, ProofShape.lift_subst_lift] using
      (ConstantHeadDeletion.drop (A := A.subst τ) (e := e.subst τ) (x := x.subst τ))
  | app _ ih => exact .app (ih τ)
  | lam _ ih => exact .lam (ih τ.lift)
  | identity _ ih => exact .identity (ih τ)

/-- An unconsumed deletion always lies behind a lambda at the ordinary head.
Consequently no primitive can inspect the enclosing term before beta exposes
the tracked payload. -/
theorem ConstantHeadDeletion.eq_or_lambda (H : ConstantHeadDeletion e e') :
    e = e' ∨ ∃ A b args, e = ProofShape.mkApps (.lam A b) args := by
  induction H with
  | refl => exact .inl rfl
  | drop => exact .inr ⟨_, _, [_], rfl⟩
  | app _ ih =>
    rcases ih with rfl | ⟨A, b, args, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨A, b, args ++ [_], (ProofShape.mkApps_snoc ..).symm⟩
  | lam => exact .inr ⟨_, _, [], rfl⟩
  | identity => exact .inr ⟨_, _, [_], rfl⟩

variable [Params]

/-- A final exposed carrier has consumed the deleted wrapper, so the
simulated endpoint is exactly the original endpoint. -/
theorem ConstantHeadDeletion.exposed_eq (H : ConstantHeadDeletion e e')
    (HE : CarrierExposure e) : e = e' := by
  rcases H.eq_or_lambda with E | ⟨A, b, args, E⟩
  · exact E
  · exact (HE.not_lambda_spine A b args E).elim

/-- Beta computation simulates a tracked constant deletion, allowing the
endpoints to differ until the deleted wrapper is consumed. -/
theorem ConstantHeadDeletion.beta (H : ConstantHeadDeletion e lower) (R : BetaRed e out) :
    ∃ lowerOut, BetaRed lower lowerOut ∧ ConstantHeadDeletion out lowerOut := by
  induction R generalizing lower with
  | refl => exact ⟨_, .refl, H⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, R₁, H₁⟩ := ih₁ H
    obtain ⟨last, R₂, H₂⟩ := ih₂ H₁
    exact ⟨last, R₁.trans R₂, H₂⟩
  | app RF RX ihf ihx =>
    cases H with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | drop =>
      obtain ⟨A', body', rfl, _, RB⟩ := RF.lam_inv
      obtain ⟨e', RE, rfl⟩ := RB.liftN_inv
      exact ⟨e', RE, .drop⟩
    | app H =>
      obtain ⟨f', RF', HF⟩ := ihf H
      exact ⟨_, .app RF' RX, .app HF⟩
    | identity H =>
      obtain ⟨A', rfl, _⟩ :=
        (show ScopedCompute (PiInertStage Definitions.empty 0) [] _ _ from .beta RF).pi_inert_identity_lam
      obtain ⟨x', RX', HX⟩ := ihx H
      exact ⟨_, .app RF RX', .identity HX⟩
  | proj R _ => cases H with | refl => exact ⟨_, .proj R, .refl⟩
  | lam RA RB _ ih =>
    cases H with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam H =>
      obtain ⟨b', RB', HB⟩ := ih H
      exact ⟨_, .lam RA RB', .lam HB⟩
  | forallE RA RB _ _ => cases H with | refl => exact ⟨_, .forallE RA RB, .refl⟩
  | beta =>
    cases H with
    | refl => exact ⟨_, .beta, .refl⟩
    | drop =>
      refine ⟨_, .refl, ?_⟩
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
      exact .refl
    | app H =>
      cases H with
      | refl => exact ⟨_, .beta, .refl⟩
      | lam H =>
        refine ⟨_, .beta, ?_⟩
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H.subst (ProofShape.Subst.one _)
    | identity H =>
      exact ⟨_, .beta, by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons] using H⟩

omit [Params] in
/-- Deleting the wrapper itself is a compatible beta reduction. This gives
typing of the lower expression directly from typing of the original one. -/
theorem ConstantHeadDeletion.reduce (H : ConstantHeadDeletion e lower) : BetaRed e lower := by
  induction H with
  | refl => exact .refl
  | @drop A x e =>
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using (BetaRed.beta (A := A) (b := e.liftN 1) (a := x))
  | app _ ih => exact .app ih .refl
  | lam _ ih => exact .lam .refl ih
  | identity _ ih => exact .app .refl ih

private theorem typed_lam_domain (HT : TypedSource Δ (.lam A body)) :
    ∃ u, DomainSort Δ A u := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, hA⟩, _, _⟩ := ht.lam_inv henv hΓ
  exact ⟨u, Γ, A₀, hΓ, rfl, hA, EA⟩

private theorem typed_constant_lambda_count_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (.app (.lam A (e.liftN 1)) x))
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.lam A (e.liftN 1)) outF) :
    ∃ A' e' j, j ≤ cf ∧ outF = .lam A' (e'.liftN 1) ∧
      ScopedComputeCount (PiInertStage D n) j Δ e e' := by
  obtain ⟨u, SD⟩ := typed_lam_domain ((ScopedHole.appFn .hole x).typed HT)
  have HTlower : TypedSource Δ e := HT.pi_inert_compute heq hs
    (ScopedCompute.beta (Step := PiInertStage D n) ConstantHeadDeletion.drop.reduce)
  obtain ⟨Γ, actual, T, hΓ, rfl, ht, rfl⟩ := HTlower
  obtain ⟨actualA, hA, rfl⟩ := SD.realize hΓ
  obtain ⟨A', e', j, hj, _, _, EF, RJ⟩ :=
    pi_inert_constant_lambda_count_readout heq hs hΓ hA ht rfl RF
  exact ⟨_, _, j, hj, EF, RJ⟩

/-- A typed counted Pi-inert computation simulates a tracked constant
wrapper deletion at the same stage and scope without increasing its count.
Actual source typing reconstitutes the lower payload at every surviving
constant wrapper; no guarded path is substituted. -/
theorem ConstantHeadDeletion.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ConstantHeadDeletion e lower) (HT : TypedSource Δ e)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ e out) :
    ∃ lowerOut k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ lower lowerOut ∧
      ConstantHeadDeletion out lowerOut := by
  induction R generalizing lower with
  | base HR =>
    rcases H.eq_or_lambda with rfl | ⟨A, b, args, rfl⟩
    · exact ⟨_, 1, by omega, .base HR, .refl⟩
    · rcases HR.2 with HP | ⟨u, HS⟩
      · exact (lambda_spine_not_primitive A b args HP).elim
      · cases args using List.snoc_induction with
        | nil => cases HS
        | snoc args a => rw [ProofShape.mkApps_snoc] at HS; cases HS
  | beta R =>
    obtain ⟨lowerOut, RB, HB⟩ := H.beta R
    exact ⟨lowerOut, 0, by omega, .beta RB, HB⟩
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨mid, j, hj, RJ, HJ⟩ := ih₁ H HT
    obtain ⟨last, k, hk, RK, HK⟩ := ih₂ HJ (HT.pi_inert_compute heq hs R₁.forget)
    exact ⟨last, j+k, by omega, RJ.trans RK, HK⟩
  | @app cf Δ f f' cx a a' RF RX ihf ihx =>
    have HTarg := (ScopedHole.appArg f .hole).typed HT
    cases H with
    | refl => exact ⟨_, _, by omega, .app RF RX, .refl⟩
    | drop =>
      obtain ⟨A', e', j, hj, rfl, RJ⟩ := typed_constant_lambda_count_readout heq hs HT RF
      exact ⟨e', j, by omega, RJ, .drop⟩
    | app H =>
      obtain ⟨f', j, hj, RJ, HJ⟩ := ihf H ((ScopedHole.appFn .hole a).typed HT)
      exact ⟨_, _, by omega, .app RJ RX, .app HJ⟩
    | identity H =>
      obtain ⟨A', rfl, _⟩ := RF.forget.pi_inert_identity_lam
      obtain ⟨x', j, hj, RJ, HJ⟩ := ihx H HTarg
      exact ⟨_, _, by omega, .app RF RJ, .identity HJ⟩
  | proj R _ => cases H with | refl => exact ⟨_, _, by omega, .proj R, .refl⟩
  | lam RA RB _ ih =>
    cases H with
    | refl => exact ⟨_, _, by omega, .lam RA RB, .refl⟩
    | lam H =>
      obtain ⟨b', j, hj, RJ, HJ⟩ := ih H ((ScopedHole.lamBody _ .hole).typed HT)
      exact ⟨_, _, by omega, .lam RA RJ, .lam HJ⟩
  | forallE RA RB _ _ => cases H with | refl => exact ⟨_, _, by omega, .forallE RA RB, .refl⟩

omit [Params] in
/-- Tracked surrounding holes preserve constant deletion, including lambda
bodies and identity payloads. -/
theorem TrackedHeadHole.constant_deletion {C : ScopedHole Δ Θ}
    (HC : TrackedHeadHole C) (H : ConstantHeadDeletion e e') :
    ConstantHeadDeletion (C.plug e) (C.plug e') := by
  induction HC with
  | hole => exact H
  | appFn _ ih => exact .app ih
  | lamBody _ ih => exact .lam ih
  | identity _ ih => exact .identity ih

/-- Every actual typed mixed continuation ending at an exposed carrier
admits deletion at its input. Its original source typings justify simulation
of each application path. The competitor keeps the exact continuation
predicate; no extra typing condition is imposed on its endpoints. -/
theorem PiInertTypedContinuationRun.constant_deletion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HK : PiInertTypedContinuationRun D Ω out Δ K e cost)
    (HE : CarrierExposure out) (H : ConstantHeadDeletion e lower) :
    ∃ k, k ≤ cost ∧ K lower k := by
  induction HK generalizing lower with
  | terminal HT => exact ⟨0, by omega, (H.exposed_eq HE).symm, rfl⟩
  | @application Δ e Θ τ args n cs e' K ck HToriginal W HT R HK ih =>
    obtain ⟨endpoint', j, hj, RJ, HJ⟩ :=
      ((H.subst τ).mkApps args).compute heq hs HT R
    obtain ⟨k, hk, HK'⟩ := ih HJ
    exact ⟨j+k, by omega, n, j, endpoint', k, rfl, RJ, HK'⟩
  | retained HT SD RD WI HK ih =>
    exact ih ((ConstantHeadDeletion.lam H).mkApps _)

/-- Simulate deletion through the current typed path and its entire actual
mixed continuation, preserving the exact final output and continuation
predicate at no greater combined primitive cost. -/
theorem pi_inert_constant_frames_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source) (H : ConstantHeadDeletion source lower)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HE : CarrierExposure out) :
    ∃ endpoint' j k, j+k ≤ cb+ck ∧
      ScopedComputeCount (PiInertStage D n) j Δ lower endpoint' ∧ K endpoint' k := by
  obtain ⟨endpoint', j, hj, RJ, HJ⟩ := H.compute heq hs HT R
  obtain ⟨k, hk, HK'⟩ := HK.constant_deletion heq hs HE HJ
  exact ⟨endpoint', j, k, by omega, RJ, HK'⟩

/-- Constant expansion cannot occur at a tracked root in a typed minimum
ending at an exposed carrier, regardless of how many enclosing mixed frames
remain. The actual prefix and primitive supply the tail-source typing needed
for deletion; removing the expansion saves its unit primitive cost. -/
theorem pi_inert_frames_minimum_no_constant {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ original) (HE : CarrierExposure out)
    (HC : TrackedHeadHole C)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (C.plug source))
    (HR : PiInertStage D n Θ source target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) : ¬ ConstantExpansion source target := by
  intro H
  have HD : ConstantHeadDeletion (C.plug target) (C.plug source) := by
    apply HC.constant_deletion
    cases H with | intro _ => exact .drop
  have HTtarget := (HT.pi_inert_compute heq hs RP.forget).pi_inert_compute heq hs
    (C.compute (.base HR))
  obtain ⟨endpoint', j, k, hjk, RJ, HK'⟩ :=
    pi_inert_constant_frames_bypass heq hs HTtarget HD RT HK HE
  have HM := hmin n (cp+j) endpoint' k (RP.trans RJ) HK'
  omega

end Lean4Lean.VEnv.Strengthening
