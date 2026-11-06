import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmbeddedHistory

/-! # Keep actual supplied arguments through embedded eta descent

Component-only eta consumption returns to its parent scope with every supplied
argument retained, including when the selected Eq prefix was underfilled.
The next minimum keeps the original suffix and unrestricted competitors.
Retained component-only bodies advance to their actual final endpoint and
annotation, charging only the original outer continuation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private native_eta_body_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixExecution
variable [Params]

/-- In a globally minimal actual eta execution, the component-only body case
advances to the exact completed post-beta source with a strictly smaller typed
minimum. Otherwise a completed non-level body root is retained within a strictly
smaller budget. Competitors keep the original continuation predicate and may
use any finite stage; the agreement needed for consumption is derived from
the actual supplied argument, not from an arbitrary context substitution. -/
theorem EqTargetPrefixEmbedding.consumed_eta_spine_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))))
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body'))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) (x' :: rest'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') rest') endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+cf+ca+cs+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ source endpoint' → K endpoint' k → cost ≤ j+k) :
    ((∃ nextLs nextArgs,
        ProofShape.mkApps (body'.inst x') rest' = ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs ∧
        nextArgs.length = pre.length + 1 + rest.length ∧
        EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs)) ∧
      cs+ck < cost ∧ PiInertTypedContinuationMinimum D Ω out Δ
        (ProofShape.mkApps (body'.inst x') rest') (cs+ck)) ∨
    (∃ cd cb bodyStage, cd+cb = cf ∧ cb < cost ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      EmbeddedTargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  obtain ⟨cd, cb, bodyStage, hc, RD, RB, Hnext | Hcut⟩ :=
    HP.consumed_eta_spine_execution heq hs hΓ ht HTwhole RN SD RF RX
  · have Reta : ScopedComputeCount (PiInertStage D n) 1 Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest))
        (ProofShape.mkApps (.lam A
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (x :: rest)) := by
      simpa only [ProofShape.mkApps_append, Nat.add_zero] using
        (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := x :: rest))
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam A' body') (x' :: rest'))
        (ProofShape.mkApps (body'.inst x') rest') := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n) (Δ := Δ)
          (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
            (ScopedArgumentsCount.refl (args := rest'))
    have Rprefix : ScopedComputeCount (PiInertStage D n) (cp+1+cf+ca) Δ source
        (ProofShape.mkApps (body'.inst x') rest') := by
      simpa only [Nat.add_zero, Nat.add_assoc] using ((RP.trans Reta).trans (RF.mkApps RX)).trans Rbeta
    have hreverse := hmin n _ endpoint ck (Rprefix.trans RS) HK.holds
    have heqCost : cost = cp+1+cf+ca+cs+ck := by omega
    have HTnext := HTwhole.pi_inert_compute heq hs ((Reta.trans (RF.mkApps RX)).trans Rbeta).forget
    refine .inl ⟨Hnext, by omega, K, n, cs, ck, endpoint, HTnext, RS, HK, rfl, ?_⟩
    intro later j endpoint' k RJ HK'
    have RR := (Rprefix.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := hmin (max n later) _ endpoint' k RR HK'
    omega
  · exact .inr ⟨cd, cb, bodyStage, hc, by omega, RD, RB, Hcut⟩

/-- Move a minimum to the body at the actual retained-lambda endpoint. Every
competitor is wrapped with the final annotation and supplied arguments, then
prefixed by the already executed path. The selected run adds just that retained
frame; it does not reify the preceding body computation as an application. -/
theorem pi_inert_retained_endpoint_minimum
    (HT : TypedSource (A :: Δ) body) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.lam A body) args))
    (HK : PiInertTypedContinuationRun D Ω out Δ K (ProofShape.mkApps (.lam A body) args) ck)
    (hcost : cp+ck ≤ cost)
    (hmin : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint →
      K endpoint k → cost ≤ j+k) :
    cost = cp+ck ∧ PiInertTypedContinuationMinimum D Ω out (A :: Δ) body ck := by
  have hexact := hmin n cp _ ck RP HK.holds
  refine ⟨by omega, (fun body k => K (ProofShape.mkApps (.lam A body) args) k),
    0, 0, ck, body, HT, .beta .refl, ?_, by omega, ?_⟩
  · exact .retained HT SD (ScopedComputeCount.beta (Step := PiInertStage D 0) BetaRed.refl)
      ContextRenaming.identity.interpretation HK
  · intro later j tail k RJ HL
    have RR : ScopedComputeCount (PiInertStage D later) j Δ
        (ProofShape.mkApps (.lam A body) args) (ProofShape.mkApps (.lam A tail) args) := by
      simpa only [Nat.zero_add, Nat.add_zero] using
        (ScopedComputeCount.lam (ScopedComputeCount.beta BetaRed.refl) RJ).mkApps
          (ScopedArgumentsCount.refl (args := args))
    have HB := hmin (max n later) _ _ k
      ((RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
        (RR.mono (pi_inert_stage_mono (Nat.le_max_right n later)))) HL
    omega

/-- A retained eta whose body changes only components advances to that exact
body endpoint under the actual final annotation. Completion transports through
the recorded annotation history, and its minimum costs only the original outer
continuation. Otherwise the original-scope body has an embedded non-level cut.
This covers arbitrary supplied arguments and does not assume the body is fresh. -/
theorem EqTargetPrefixEmbedding.retained_eta_spine_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))))
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body'))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca pending args')
    (HK : PiInertTypedContinuationRun D Ω out Δ K (ProofShape.mkApps (.lam A' body') args') ck)
    (hcost : cp+1+cf+ca+ck ≤ cost)
    (hmin : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint →
      K endpoint k → cost ≤ j+k) :
    (∃ nextLs nextArgs, body' = ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs ∧
      nextArgs.length = pre.length + 1 ∧
      EqTargetPrefixEmbedding Γ v w original (A' :: Δ) (ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs) ∧
      ck < cost ∧ PiInertTypedContinuationMinimum D Ω out (A' :: Δ) body' ck) ∨
    (∃ cd cb bodyStage, cd+cb = cf ∧ cb < cost ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      EmbeddedTargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  have HPbody := (HP.take_prefix heq hs hΓ).eta heq hs hΓ ht RN SD
  have HTpre : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) :=
    typed_spine_head (by simpa only [ProofShape.mkApps_append] using HTwhole)
  have HTfresh := native_eta_body_typed
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) HTpre RN SD
  obtain ⟨cd, cb, bodyStage, hc, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    HTpre (.intro RN SD) RF
  have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
      ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
  rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ HTfresh) (ES ▸ RB) with
    ⟨nextLs, nextArgs, EO, _, HA, HPend⟩ | Hcut
  · have Reta : ScopedComputeCount (PiInertStage D n) 1 Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending))
        (ProofShape.mkApps (.lam A
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) pending) := by
      simpa only [ProofShape.mkApps_append, Nat.add_zero] using
        (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))
    have Rprefix := (RP.trans Reta).trans (RF.mkApps RX)
    have HTend := HTwhole.pi_inert_compute heq hs (Reta.trans (RF.mkApps RX)).forget
    have HTbody := (ScopedHole.lamBody A' .hole).typed (typed_spine_head HTend)
    have SD' : DomainSort Δ A' u := by
      obtain ⟨Ξ, a, hΞ, EΞ, ha, Ea⟩ := SD
      obtain ⟨a', HE, EE⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
        hΞ ha EΞ Ea RD.forget
      exact ⟨Ξ, a', hΞ, EΞ, HE.hasType.2, EE⟩
    have HP' := HPend.context_history heq hs hΓ (.step (.head RD.forget) .refl)
    obtain ⟨_, HM⟩ := pi_inert_retained_endpoint_minimum HTbody SD' Rprefix HK (cost := cost) (by omega) hmin
    refine .inl ⟨nextLs, nextArgs, EO, ?_, EO ▸ HP', by omega, HM⟩
    have HB := HA.length_eq
    simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil, Nat.zero_add] using HB.symm
  · exact .inr ⟨cd, cb, bodyStage, hc, by omega, RD, RB, ES.symm ▸ Hcut⟩

end Lean4Lean.VEnv.Strengthening
