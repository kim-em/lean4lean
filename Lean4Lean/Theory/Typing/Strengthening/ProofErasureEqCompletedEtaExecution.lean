import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIteratedConsumption

/-! # Derive completion from the actual counted eta execution

The lambda readout keeps body computation in its original binder context.
A body that only changes components gives a completed consumed endpoint.
Otherwise its actual first non-level spine root has a derived completion,
with the original counted prefix and suffix retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- The actual first non-level Eq-spine root, with target completion derived
from its preceding component history. This retains the original path endpoints,
root stage, pending arguments and count bound. Classifying the completed root
and following later arbitrary wrapper execution remain separate obligations. -/
def IteratedCompletedEqSpineCut (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (n : Nat) (Δ : List ProofShape)
    (source endpoint : ProofShape) (budget : Nat) : Prop :=
  ∃ ls pre pending target cp ct, cp+1+ct ≤ budget ∧
    ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
    PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ¬ LevelPrimitive univs (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) endpoint ∧
    IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)

/-- A counted computation from a completed Eq spine either preserves completion
at its exact endpoint or encounters a completed non-level root on that same
path. Completion at the root is obtained by reifying its actual component
history, not assumed from root typing. -/
theorem IteratedAmbientEqCompletion.counted_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint) :
    (∃ ls' args', endpoint = ProofShape.mkApps (.const ``Eq.rec ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args' ∧
      IteratedAmbientEqCompletion Γ v w original Δ endpoint) ∨
    IteratedCompletedEqSpineCut D Γ v w original n Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint cost := by
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls', args', EO, HL, HA⟩ | ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, HR, HN, RT⟩
  · have HT := EO ▸ HP.typed.pi_inert_compute heq hs R.forget
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA args'.length
    exact .inl ⟨ls', args', EO, HL, HA, by simpa only [List.take_length, ← EO] using HH⟩
  · have HT := RP.forget.spine_cut_source_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) HP.typed
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA pre.length
    exact .inr ⟨ls', pre, pending, target, cp, ct, hc, RP, HR, HN, RT,
      by simpa only [List.take_left] using HH⟩

/-- Taking a prefix of a completed source keeps the exact current scope.
This is the zero-step case of actual component preservation. -/
theorem IteratedAmbientEqCompletion.take_prefix {D : Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending))) :
    IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) := by
  have HH := HP.compute_components heq hs hΓ (.rfl (fun _ _ => by rfl))
    (typed_const_levels_wf HP.typed)
    (show List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) (pre ++ pending) (pre ++ pending) from
      .rfl (fun _ _ => .refl)) pre.length
  simpa only [List.take_left] using HH

/-- An actually supplied next argument guarantees an unfilled target slot.
The fresh eta body's completion therefore follows from the whole source's
completion, even through iterated unused insertions. -/
theorem IteratedAmbientEqCompletion.eta_of_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : IteratedAmbientEqCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u) :
    IteratedAmbientEqCompletion Γ v w original (A :: Δ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) := by
  obtain ⟨ls₀, args₀, EE, hlen⟩ := HP.arity
  obtain ⟨_, _, EA⟩ := ProofShape.const_spine_inj EE
  have hshort : pre.length < original.length := by
    rw [← EA, List.length_append, List.length_cons] at hlen
    omega
  exact (HP.take_prefix heq hs hΓ).eta heq hs hΓ ht hshort RN SD

/-- In an actual first-beta decomposition, changing annotations and arguments
may be arbitrary. The exact lambda history either supplies a completed
post-beta spine, or its original-scope body path has a completed non-level
root. This derives the consumption branch from counted execution; no body
component-history hypothesis or target-image agreement is added. -/
theorem IteratedAmbientEqCompletion.consumed_eta_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : IteratedAmbientEqCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body'))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) (x' :: rest')) :
    ∃ cd cb bodyStage, cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∨
        IteratedCompletedEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  have HPpre := HP.take_prefix heq hs hΓ
  have HPbody := HP.eta_of_supply heq hs hΓ ht RN SD
  obtain ⟨cd, cb, bodyStage, hc, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    HPpre.typed (.intro RN SD) RF
  refine ⟨cd, cb, bodyStage, hc, RD, RB, ?_⟩
  have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
      ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
      ProofShape.mkApps]
  rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ RB) with
    ⟨bodyLs, rawBody, EO, HL, HA, _⟩ | Hcut
  · have HTbody := EO ▸ HPbody.typed.pi_inert_compute heq hs RB.forget
    cases RX with
    | cons RX RXS =>
      have Hnext := HP.consume_eta_components heq hs hΓ ht RN SD HL HA HTbody RX.forget RXS.forget
      exact .inl (by simpa only [EO, ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using Hnext)
  · exact .inr (ES.symm ▸ Hcut)


/-- In a globally minimal actual eta execution, the component-only body case
advances to the exact completed post-beta source with a strictly smaller typed
minimum. Otherwise a completed non-level body root is retained within a strictly
smaller budget. Competitors keep the original continuation predicate and may
use any finite stage; the agreement needed for consumption is derived from
the actual supplied argument, not from an arbitrary context substitution. -/
theorem IteratedAmbientEqCompletion.consumed_eta_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : IteratedAmbientEqCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
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
    (IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∧
      cs+ck < cost ∧ PiInertTypedContinuationMinimum D Ω out Δ
        (ProofShape.mkApps (body'.inst x') rest') (cs+ck)) ∨
    (∃ cd cb bodyStage, cd+cb = cf ∧ cb < cost ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      IteratedCompletedEqSpineCut D Γ v w original bodyStage (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  obtain ⟨cd, cb, bodyStage, hc, RD, RB, Hnext | Hcut⟩ :=
    HP.consumed_eta_execution heq hs hΓ ht RN SD RF RX
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
    refine .inl ⟨Hnext, by omega, K, n, cs, ck, endpoint, Hnext.typed, RS, HK, rfl, ?_⟩
    intro later j endpoint' k RJ HK'
    have RR := (Rprefix.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := hmin (max n later) _ endpoint' k RR HK'
    omega
  · exact .inr ⟨cd, cb, bodyStage, hc, by omega, RD, RB, Hcut⟩


/-- Split the actual entire suffix of a supplied eta expansion. In the retained
case, completion or the selected body root is kept in the original binder
context alongside the exact annotation history. In the consumed case,
completion is derived at the exact beta endpoint or a completed body root is
selected. Both cases retain the actual lambda, argument and suffix paths and
their original count bound. Moving a retained completed body into a changed
annotation context is deliberately not inferred from ordinary context typing. -/
theorem IteratedAmbientEqCompletion.eta_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : IteratedAmbientEqCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.lam A
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (x :: rest)) endpoint) :
    (∃ A' body' args' cf ca cd cb bodyStage, cf+ca ≤ cost ∧ cd+cb = cf ∧
      endpoint = ProofShape.mkApps (.lam A' body') args' ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) args' ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (IteratedAmbientEqCompletion Γ v w original (A :: Δ) body' ∨
        IteratedCompletedEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb)) ∨
    (∃ A' body' x' rest' cf ca cs cd cb bodyStage, cf+ca+cs ≤ cost ∧ cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) (x' :: rest') ∧
      ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') rest') endpoint ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∨
        IteratedCompletedEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb)) := by
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', body', x', rest', cf, ca, cs, hc, RF, RX, RS⟩
  · have HPpre := HP.take_prefix heq hs hΓ
    have HPbody := HP.eta_of_supply heq hs hΓ ht RN SD
    obtain ⟨cd, cb, bodyStage, hcb, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
      HPpre.typed (.intro RN SD) RF
    refine .inl ⟨A', body', args', cf, ca, cd, cb, bodyStage, hc, hcb, EO, RF, RX, RD, RB, ?_⟩
    have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
        ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
      simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
        ProofShape.mkApps]
    rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ RB) with
      ⟨_, _, _, _, _, HPend⟩ | Hcut
    · exact .inl HPend
    · exact .inr (ES.symm ▸ Hcut)
  · obtain ⟨cd, cb, bodyStage, hcb, RD, RB, Hbody⟩ :=
      HP.consumed_eta_execution heq hs hΓ ht RN SD RF RX
    exact .inr ⟨A', body', x', rest', cf, ca, cs, cd, cb, bodyStage,
      hc, hcb, RF, RX, RS, RD, RB, Hbody⟩

end Lean4Lean.VEnv.Strengthening
