import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTrackedHeadHole

/-! # Identity deletion through mixed continuation frames

Track a removed identity through function positions, retained lambda bodies,
and other identity payloads. Simulation changes endpoints, keeps each guarded
computation in its original scope, and never increases its primitive count.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private lambda_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta

/-- Delete one identity at a tracked head position, or retain equality after
that identity has been consumed. Annotations and ordinary arguments agree
exactly; other identity wrappers may surround the tracked payload. -/
inductive IdentityHeadDeletion : ProofShape → ProofShape → Prop where
  | refl : IdentityHeadDeletion e e
  | drop : IdentityHeadDeletion (.app (.lam A (.bvar 0)) e) e
  | app : IdentityHeadDeletion f f' → IdentityHeadDeletion (.app f a) (.app f' a)
  | lam : IdentityHeadDeletion b b' → IdentityHeadDeletion (.lam A b) (.lam A b')
  | identity : IdentityHeadDeletion e e' →
      IdentityHeadDeletion (.app (.lam A (.bvar 0)) e) (.app (.lam A (.bvar 0)) e')

/-- Pending arguments preserve the tracked deletion. -/
theorem IdentityHeadDeletion.mkApps (H : IdentityHeadDeletion f f') (args : List ProofShape) :
    IdentityHeadDeletion (ProofShape.mkApps f args) (ProofShape.mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact H
  | cons a args ih => exact ih (.app H)

/-- Raw endpoint substitution preserves the tracked deletion without any
substitution principle for primitive guards. -/
theorem IdentityHeadDeletion.subst (H : IdentityHeadDeletion e e') (τ : ProofShape.Subst) :
    IdentityHeadDeletion (e.subst τ) (e'.subst τ) := by
  induction H generalizing τ with
  | refl => exact .refl
  | drop => exact .drop
  | app _ ih => exact .app (ih τ)
  | lam _ ih => exact .lam (ih τ.lift)
  | identity _ ih => exact .identity (ih τ)

/-- An unconsumed deletion always lies behind a lambda at the ordinary head.
Consequently no primitive can inspect the enclosing term before beta exposes
the tracked payload. -/
theorem IdentityHeadDeletion.eq_or_lambda (H : IdentityHeadDeletion e e') :
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

/-- A final exposed carrier has consumed the deleted identity, so the
simulated endpoint is exactly the original endpoint. -/
theorem IdentityHeadDeletion.exposed_eq (H : IdentityHeadDeletion e e')
    (HE : CarrierExposure e) : e = e' := by
  rcases H.eq_or_lambda with E | ⟨A, b, args, E⟩
  · exact E
  · exact (HE.not_lambda_spine A b args E).elim

/-- Beta computation simulates a tracked identity deletion, allowing the
endpoints to differ until the deleted identity is consumed. -/
theorem IdentityHeadDeletion.beta (H : IdentityHeadDeletion e lower) (R : BetaRed e out) :
    ∃ lowerOut, BetaRed lower lowerOut ∧ IdentityHeadDeletion out lowerOut := by
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
      obtain ⟨A', rfl, _⟩ :=
        (show ScopedCompute (PiInertStage Definitions.empty 0) [] _ _ from .beta RF).pi_inert_identity_lam
      exact ⟨_, RX, .drop⟩
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
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons]
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

/-- Every counted Pi-inert computation simulates deletion in the same scope
and at the same stage, with a possibly smaller outer primitive count. -/
theorem IdentityHeadDeletion.compute (H : IdentityHeadDeletion e lower)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ e out) :
    ∃ lowerOut k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ lower lowerOut ∧
      IdentityHeadDeletion out lowerOut := by
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
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, j, hj, RJ, HJ⟩ := ih₁ H
    obtain ⟨last, k, hk, RK, HK⟩ := ih₂ HJ
    exact ⟨last, j+k, by omega, RJ.trans RK, HK⟩
  | app RF RX ihf ihx =>
    cases H with
    | refl => exact ⟨_, _, by omega, .app RF RX, .refl⟩
    | drop =>
      obtain ⟨A', rfl, _⟩ := RF.forget.pi_inert_identity_lam
      exact ⟨_, _, by omega, RX, .drop⟩
    | app H =>
      obtain ⟨f', j, hj, RJ, HJ⟩ := ihf H
      exact ⟨_, _, by omega, .app RJ RX, .app HJ⟩
    | identity H =>
      obtain ⟨A', rfl, _⟩ := RF.forget.pi_inert_identity_lam
      obtain ⟨x', j, hj, RJ, HJ⟩ := ihx H
      exact ⟨_, _, by omega, .app RF RJ, .identity HJ⟩
  | proj R _ => cases H with | refl => exact ⟨_, _, by omega, .proj R, .refl⟩
  | lam RA RB _ ih =>
    cases H with
    | refl => exact ⟨_, _, by omega, .lam RA RB, .refl⟩
    | lam H =>
      obtain ⟨b', j, hj, RJ, HJ⟩ := ih H
      exact ⟨_, _, by omega, .lam RA RJ, .lam HJ⟩
  | forallE RA RB _ _ => cases H with | refl => exact ⟨_, _, by omega, .forallE RA RB, .refl⟩

omit [Params] in
/-- A tracked surrounding hole preserves identity deletion even when its
payload lies under several binders or inside other identity wrappers. -/
theorem TrackedHeadHole.identity_deletion {C : ScopedHole Δ Θ}
    (HC : TrackedHeadHole C) (H : IdentityHeadDeletion e e') :
    IdentityHeadDeletion (C.plug e) (C.plug e') := by
  induction HC with
  | hole => exact H
  | appFn _ ih => exact .app ih
  | lamBody _ ih => exact .lam ih
  | identity _ ih => exact .identity ih

/-- A finite mixed continuation ending at an exposed carrier tolerates a
tracked identity deletion at its input. All endpoint substitutions and retained
annotations remain fixed; only intermediate endpoints and counts change. -/
theorem PiInertContinuationFrames.identity_deletion
    (HF : PiInertContinuationFrames D Ω out Δ K) (HE : CarrierExposure out)
    (H : IdentityHeadDeletion e lower) (HK : K e cost) :
    ∃ k, k ≤ cost ∧ K lower k := by
  induction HF generalizing e lower cost with
  | terminal =>
    obtain ⟨rfl, rfl⟩ := HK
    exact ⟨0, by omega, H.exposed_eq HE |>.symm, rfl⟩
  | @application Δ Θ τ K args W HF ih =>
    obtain ⟨n, cs, endpoint, ck, rfl, R, HK⟩ := HK
    obtain ⟨endpoint', j, hj, RJ, HJ⟩ := ((H.subst τ).mkApps args).compute R
    obtain ⟨k, hk, HK'⟩ := ih HJ HK
    exact ⟨j+k, by omega, n, j, endpoint', k, rfl, RJ, HK'⟩
  | @retained Δ A u n cd A' K args SD RD WI HF ih =>
    exact ih ((IdentityHeadDeletion.lam H).mkApps args) HK

/-- Jointly change the current computation endpoint and all enclosing
continuation endpoints to bypass a tracked identity. The fixed continuation
predicate and exposed terminal result are preserved at no greater total cost. -/
theorem pi_inert_identity_frames_bypass
    (HF : PiInertContinuationFrames D Ω out Δ K) (HE : CarrierExposure out)
    (H : IdentityHeadDeletion source lower)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source endpoint)
    (HK : K endpoint ck) :
    ∃ endpoint' j k, j+k ≤ cb+ck ∧
      ScopedComputeCount (PiInertStage D n) j Δ lower endpoint' ∧ K endpoint' k := by
  obtain ⟨endpoint', j, hj, RJ, HJ⟩ := H.compute R
  obtain ⟨k, hk, HK'⟩ := HF.identity_deletion HE HJ HK
  exact ⟨endpoint', j, k, by omega, RJ, HK'⟩

/-- A minimum ending at an exposed carrier excludes identity expansion at
any tracked root of its current path, through arbitrarily many mixed frames.
Removing the expansion saves its unit primitive cost, even if its wrapper
survives the current endpoint and is consumed only in a later frame. -/
theorem pi_inert_frames_minimum_no_identity {C : ScopedHole Δ Θ}
    (HF : PiInertContinuationFrames D Ω out Δ K) (HE : CarrierExposure out)
    (HC : TrackedHeadHole C)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (C.plug source))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint)
    (HK : K endpoint ck) (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ∀ Recovery, ¬ NativeIdentityExpansion Recovery Θ source target := by
  intro Recovery HI
  cases HI with
  | intro _ =>
    obtain ⟨endpoint', j, k, hjk, RJ, HK'⟩ :=
      pi_inert_identity_frames_bypass HF HE (HC.identity_deletion .drop) RT HK
    have HM := hmin n (cp+j) endpoint' k (RP.trans RJ) HK'
    omega

end Lean4Lean.VEnv.Strengthening
