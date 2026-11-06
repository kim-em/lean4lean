import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertIdentityContinuation

/-! # Constant-wrapper removal across a typed continuation

Only the wrapper's endpoint is substituted. A context interpretation supplies
actual typings for the computed annotation and payload in the continuation's
scope, where ordinary counted constant-wrapper elimination can be applied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Remove a constant wrapper before or after a typed endpoint substitution,
preserving the exact final output and not increasing the combined body/suffix
count. No substitution law for guarded computation is assumed or used. -/
theorem pi_inert_constant_spine_continuation_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (W : ContextSubstitution (proofEraseCtx Γ) Ω τ)
    (R : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx Γ)
      (ProofShape.mkApps (.app (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) x) args) body')
    (S : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (HE : CarrierExposure out) :
    ∃ endpoint j k, j+k ≤ cb+cs ∧
      ScopedComputeCount (PiInertStage D m) j (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ e) args) endpoint ∧
      ScopedComputeCount (PiInertStage D n) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out := by
  change ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx Γ)
    (ProofShape.mkApps (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) (x :: args)) body' at R
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨rawA, rawB, args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨rawA, rawB, x', xs', cf, ca, ct, hc, RF, RX, RT⟩
  · obtain ⟨A', e', ce, hce, HA, He, EF, RE⟩ :=
      pi_inert_constant_lambda_count_readout heq hs hΓ hA ht rfl RF
    cases EF
    cases RX with
    | @cons cx _ x' cr _ rest _ RX =>
      obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
      have hA' := HA.hasType.2.subst henv.orderedStrong WS hΓ₀
      have he' := He.hasType.2.subst henv.orderedStrong WS hΓ₀
      have EA := proofErase_subst_with hΓ₀ WS HA.hasType.2 ES
      have Ee := proofErase_subst_with hΓ₀ WS He.hasType.2 ES
      have S' : ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Γ₀)
          (ProofShape.mkApps
            (.app (.lam (proofErase Γ₀ (A'.subst σ)) ((proofErase Γ₀ (e'.subst σ)).liftN 1)) (x'.subst τ))
            (rest.map (fun a => a.subst τ) ++ pending)) out := by
        simpa only [EO, EΓ₀, EA, Ee, ProofShape.subst_mkApps, ProofShape.subst,
          ProofShape.lift_subst_lift, List.map_cons, ProofShape.mkApps, ← ProofShape.mkApps_append] using S
      obtain ⟨k, hk, SK⟩ := pi_inert_constant_spine_count_eliminate
        heq hs hΓ₀ hA' he' HE.not_lambda_spine S'
      refine ⟨_, _, k, by omega, RE.mkApps RX, ?_⟩
      simpa only [EΓ₀, Ee, ProofShape.subst_mkApps, ProofShape.mkApps_append] using SK
  · obtain ⟨A', e', ce, hce, _, _, EF, RE⟩ :=
      pi_inert_constant_lambda_count_readout heq hs hΓ hA ht rfl RF
    cases EF
    cases RX with
    | cons _ RX =>
      refine ⟨body', _, cs, by omega, (RE.mkApps RX).trans (n := ct) ?_, S⟩
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using RT

/-- The standard constant-expansion primitive can be bypassed through a
typed continuation. Typing is needed only for its source and the endpoint
substitution, not as a native-recovery certificate for the substitution images. -/
theorem pi_inert_constant_expansion_continuation_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source) (W : ContextSubstitution Δ Ω τ)
    (H : ConstantExpansion source target)
    (R : ScopedComputeCount (PiInertStage D m) cb Δ (ProofShape.mkApps target args) body')
    (S : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (HE : CarrierExposure out) :
    ∃ endpoint j k, j+k ≤ cb+cs ∧
      ScopedComputeCount (PiInertStage D m) j Δ (ProofShape.mkApps source args) endpoint ∧
      ScopedComputeCount (PiInertStage D n) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
  cases H with
  | intro _ =>
    have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
      .sort (by trivial)
    have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
      if_neg (not_isProof_of_sort hΓ hA)
    exact pi_inert_constant_spine_continuation_bypass heq hs hΓ hA ht W
      (by simpa only [EA, ProofShape.constantExpansion] using R) S HE

/-- Constant expansion cannot be the selected body-spine root of a minimum
combined body/continuation path with a typed source and endpoint substitution.
Its removal saves the root occurrence even if the wrapper survives the body. -/
theorem pi_inert_continuation_minimum_no_constant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source) (W : ContextSubstitution Δ Ω τ)
    (RP : ScopedComputeCount (PiInertStage D m) cp Δ original (ProofShape.mkApps source args))
    (RT : ScopedComputeCount (PiInertStage D m) ct Δ (ProofShape.mkApps target args) body')
    (RS : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (hcost : cp+1+ct = cb)
    (hmin : ∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cb+cs ≤ j+k)
    (HE : CarrierExposure out) : ¬ ConstantExpansion source target := by
  intro H
  obtain ⟨endpoint, j, k, hjk, RJ, RK⟩ :=
    pi_inert_constant_expansion_continuation_bypass heq hs HT W H RT RS HE
  have HM := hmin m n (cp+j) k endpoint (RP.trans RJ) RK
  omega

end Lean4Lean.VEnv.Strengthening
