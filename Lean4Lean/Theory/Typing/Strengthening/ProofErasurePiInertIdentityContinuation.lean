import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertBodyMinimum

/-! # Identity removal through an application continuation

An identity wrapper is consumed either in the source-body computation or in
the continuation after substitution. In the latter case change the body
endpoint and the continuation together. No guarded computation is substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- An identity at a function prefix can be removed across an arbitrary raw
substitution followed by a pending application spine. The body endpoint may
change, but the final output is exact and the sum of both counts does not grow.
Only endpoint syntax is substituted; each computation stays in its own scope. -/
theorem pi_inert_identity_spine_continuation_bypass_nonlambda
    (R : ScopedComputeCount (PiInertStage D m) cb Δ
      (ProofShape.mkApps (.app (.lam A (.bvar 0)) e) args) body')
    (S : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest) :
    ∃ endpoint j k, j+k ≤ cb+cs ∧
      ScopedComputeCount (PiInertStage D m) j Δ (ProofShape.mkApps e args) endpoint ∧
      ScopedComputeCount (PiInertStage D n) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out := by
  change ScopedComputeCount (PiInertStage D m) cb Δ
    (ProofShape.mkApps (.lam A (.bvar 0)) (e :: args)) body' at R
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', b', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', b', x', xs', cf, ca, ct, hc, RF, RX, RT⟩
  · obtain ⟨A'', EF, _⟩ := RF.forget.pi_inert_identity_lam
    cases EF
    cases RX with
    | @cons cx _ e' cr _ rest RE RX =>
      have S' : ScopedComputeCount (PiInertStage D n) cs Ω
          (ProofShape.mkApps (.app (.lam (A'.subst τ) (.bvar 0)) (e'.subst τ))
            (rest.map (fun a => a.subst τ) ++ pending)) out := by
        simpa only [EO, ProofShape.subst_mkApps, ProofShape.subst, ProofShape.Subst.lift,
          List.map_cons, ProofShape.mkApps, ← ProofShape.mkApps_append] using S
      obtain ⟨k, hk, SK⟩ := S'.pi_inert_identity_spine_eliminate hout
      refine ⟨_, _, k, by omega, RE.mkApps RX, ?_⟩
      simpa only [ProofShape.subst_mkApps, ProofShape.mkApps_append] using SK
  · obtain ⟨A'', EF, _⟩ := RF.forget.pi_inert_identity_lam
    cases EF
    cases RX with
    | cons RE RX =>
      refine ⟨body', _, cs, by omega, (RE.mkApps RX).trans (n := ct) ?_, S⟩
      simpa only [ProofShape.inst, ProofShape.subst, ProofShape.Subst.liftN,
        ProofShape.Subst.one, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using RT

/-- A minimum combined body-and-continuation path has no identity expansion
at its selected body-spine root. The wrapper may be consumed before or after
the intervening substitution; either case saves its unit primitive cost. -/
theorem pi_inert_continuation_minimum_no_identity_nonlambda
    (RP : ScopedComputeCount (PiInertStage D m) cp Δ original (ProofShape.mkApps source args))
    (RT : ScopedComputeCount (PiInertStage D m) ct Δ (ProofShape.mkApps target args) body')
    (RS : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (hcost : cp+1+ct = cb)
    (hmin : ∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cb+cs ≤ j+k)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest) :
    ∀ Recovery, ¬ NativeIdentityExpansion Recovery Δ source target := by
  intro Recovery HI
  cases HI with
  | intro _ =>
    obtain ⟨endpoint, j, k, hjk, RJ, RK⟩ := pi_inert_identity_spine_continuation_bypass_nonlambda RT RS hout
    have HM := hmin m n (cp+j) k endpoint (RP.trans RJ) RK
    omega

/-- The carrier-exposure specialization, retaining the existing interface. -/
theorem pi_inert_identity_spine_continuation_bypass
    (R : ScopedComputeCount (PiInertStage D m) cb Δ
      (ProofShape.mkApps (.app (.lam A (.bvar 0)) e) args) body')
    (S : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (HE : CarrierExposure out) :
    ∃ endpoint j k, j+k ≤ cb+cs ∧
      ScopedComputeCount (PiInertStage D m) j Δ (ProofShape.mkApps e args) endpoint ∧
      ScopedComputeCount (PiInertStage D n) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out :=
  pi_inert_identity_spine_continuation_bypass_nonlambda R S HE.not_lambda_spine

/-- The carrier-exposure specialization, retaining the existing interface. -/
theorem pi_inert_continuation_minimum_no_identity
    (RP : ScopedComputeCount (PiInertStage D m) cp Δ original (ProofShape.mkApps source args))
    (RT : ScopedComputeCount (PiInertStage D m) ct Δ (ProofShape.mkApps target args) body')
    (RS : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (hcost : cp+1+ct = cb)
    (hmin : ∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cb+cs ≤ j+k)
    (HE : CarrierExposure out) :
    ∀ Recovery, ¬ NativeIdentityExpansion Recovery Δ source target :=
  pi_inert_continuation_minimum_no_identity_nonlambda RP RT RS hcost hmin HE.not_lambda_spine

end Lean4Lean.VEnv.Strengthening
