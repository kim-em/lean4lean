import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedPrefixOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixExecution

/-! # Strict descent at an actual lambda insertion inside a retained hole

Focusing alone preserves cost. Here the selected primitive inserts the lambda,
so its positive cost is removed from the fresh-body minimum. Competitors are
reassembled through the same hole and original prefix, preserving their exact
counts and the original continuation predicate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tracked_compose
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedPrefixOrigin

/-- Computation of the payload lifts through an application/binder hole
without adding primitive occurrences. Each path stays in its original scope. -/
theorem SpineBinderHole.counted {C : ScopedHole Δ Θ}
    (HC : SpineBinderHole C) (R : ScopedComputeCount Step j Θ a b) :
    ScopedComputeCount Step j Δ (C.plug a) (C.plug b) := by
  induction HC with
  | hole => exact R
  | appFn _ ih =>
    simpa only [ScopedHole.plug, Nat.add_zero] using (ih R).app (ScopedComputeCount.beta BetaRed.refl)
  | lamBody _ ih =>
    simpa only [ScopedHole.plug, Nat.zero_add] using ScopedComputeCount.lam (ScopedComputeCount.beta BetaRed.refl) (ih R)

variable [Params]

/-- An actual primitive inserting a lambda in an application/binder hole
strictly reduces the global minimum to its fresh body. The remaining entire
suffix is represented by an actual typed continuation at that body. The
pointwise competitor reconstruction retains the original outer continuation;
no guarded computation is substituted. Target agreement is not asserted. -/
theorem pi_inert_lambda_hole_body_minimum {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HC : SpineBinderHole C) (HT : TypedSource Δ original)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (C.plug f))
    (HR : PiInertStage D n Θ f (.lam A body))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug (.lam A body)) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ original tail →
      K tail k → cost ≤ j+k) :
    cp+1+ct+ck = cost ∧ ct+ck < cost ∧
    PiInertTypedContinuationMinimum D Ω out (A :: Θ) body (ct+ck) ∧
    ∃ L, PiInertTypedContinuationRun D Ω out (A :: Θ) L body (ct+ck) ∧
      PiInertPrefixClosed D (A :: Θ) L ∧
      (∀ body' k, L body' k → ∃ later j tail l, j+l = k ∧
        ScopedComputeCount (PiInertStage D later) j Δ (C.plug (.lam A body')) tail ∧ K tail l) ∧
      ∀ later j body' k, ScopedComputeCount (PiInertStage D later) j (A :: Θ) body body' →
        L body' k → ct+ck ≤ j+k := by
  have RI := HC.counted (ScopedComputeCount.base HR)
  have Rpre := RP.trans RI
  have HTlong := HT.pi_inert_compute heq hs Rpre.forget
  have hexact := hmin n (cp+1+ct) endpoint ck (Rpre.trans RT) HK.holds
  obtain ⟨B, HB, EB⟩ := tracked_compose HC
    (SpineBinderHole.lamBody (A := A) (.hole : SpineBinderHole
      (.hole : ScopedHole (A :: Θ) (A :: Θ))))
  have EB' : ∀ b, B.plug b = C.plug (.lam A b) := EB
  obtain ⟨L, HL, HLC, EL⟩ := HB.focus_path
    (by simpa only [EB'] using HTlong) (by simpa only [EB'] using RT) HK
  have EL' : ∀ body' k, L body' k → ∃ later j tail l, j+l = k ∧
      ScopedComputeCount (PiInertStage D later) j Δ (C.plug (.lam A body')) tail ∧ K tail l := by
    simpa only [EB'] using EL
  have HM : ∀ later j body' k, ScopedComputeCount (PiInertStage D later) j (A :: Θ) body body' →
      L body' k → ct+ck ≤ j+k := by
    intro later j body' k RJ HK'
    obtain ⟨m, c, tail, l, hc, RS, HK''⟩ := EL' body (j+k) (HLC later j body body' k RJ HK')
    have Rwhole := (Rpre.mono (pi_inert_stage_mono (Nat.le_max_left n m))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_right n m)))
    have HH := hmin _ _ _ _ Rwhole HK''
    omega
  have HBmin : PiInertTypedContinuationMinimum D Ω out (A :: Θ) body (ct+ck) :=
    ⟨L, 0, 0, ct+ck, body, HL.typed, .beta .refl, HL, by omega, HM⟩
  exact ⟨by omega, by omega, HBmin, L, HL, HLC, EL', HM⟩

/-- A completed native eta root inside any application/binder hole yields a
strictly smaller completed fresh-body minimum. Completion is derived at the
actual root before eta; no transport of completion through an arbitrary later
substitution is assumed. The entire outer suffix is retained as a typed body
continuation, so immediate consumption of the new binder is unnecessary. -/
theorem EqTargetPrefixCompletion.eta_hole_minimum {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) originalArgs) T)
    (HP : EqTargetPrefixCompletion Γ v w originalArgs Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : SpineBinderHole C) (HT : TypedSource Δ original)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B)) (SD : DomainSort Θ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)))
    (HR : PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (C.plug (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)))) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ original tail →
      K tail k → cost ≤ j+k) :
    cp+1+ct+ck = cost ∧ ct+ck < cost ∧
    PiInertTypedContinuationMinimum D Ω out (A :: Θ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) (ct+ck) ∧
    EqTargetPrefixCompletion Γ v w originalArgs (A :: Θ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  obtain ⟨hexact, hsmall, HM, _⟩ := pi_inert_lambda_hole_body_minimum heq hs HC HT RP HR RT HK hcost hmin
  exact ⟨hexact, hsmall, HM, HP.eta heq hs hΓ ht RN SD⟩

end Lean4Lean.VEnv.Strengthening
