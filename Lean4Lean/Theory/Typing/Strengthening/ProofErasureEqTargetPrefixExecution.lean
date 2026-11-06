import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixConsumption

/-! # Derive bounded-prefix completion from actual eta execution

The lambda readout keeps body computation in its original binder context.
A body that only changes components gives a prefix-completed consumed endpoint.
Full-source typing is retained independently from bounded-prefix ancestry;
extra source arguments need no target assignment.
Otherwise its actual first non-level spine root has a derived completion,
with the original counted prefix and suffix retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem native_eta_body_typed
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ f)
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u) :
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, he, Ee⟩ := HT
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeEtaExpansion_descent hguard) hΓ he EΓ Ee
    (ScopedCompute.base (NativeEtaExpansion.intro RN SD))
  have HTlam : TypedSource Δ (.lam A (.app (f.liftN 1) (etaArgument u))) :=
    ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩
  exact (ScopedHole.lamBody A .hole).typed HTlam


/-- The actual first non-level Eq-spine root, with bounded target completion derived
from its preceding component history, up to the target length. This retains the original path endpoints,
root stage, pending arguments and count bound. Classifying the completed root
and following later arbitrary wrapper execution remain separate obligations. -/
def TargetPrefixEqSpineCut (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (n : Nat) (Δ : List ProofShape)
    (source endpoint : ProofShape) (budget : Nat) : Prop :=
  ∃ ls pre pending target cp ct, cp+1+ct ≤ budget ∧
    ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
    PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ¬ LevelPrimitive univs (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) endpoint ∧
    EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)

/-- A counted computation from an actually typed Eq spine either preserves bounded completion
at its exact endpoint or encounters a prefix-completed non-level root on that same
path. Completion at the root is obtained by reifying its actual component
history, not assumed from root typing. -/
theorem EqTargetPrefixCompletion.counted_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HTsource : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint) :
    (∃ ls' args', endpoint = ProofShape.mkApps (.const ``Eq.rec ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args' ∧
      EqTargetPrefixCompletion Γ v w original Δ endpoint) ∨
    TargetPrefixEqSpineCut D Γ v w original n Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint cost := by
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls', args', EO, HL, HA⟩ | ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, HR, HN, RT⟩
  · have HT := EO ▸ HTsource.pi_inert_compute heq hs R.forget
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA args'.length
    exact .inl ⟨ls', args', EO, HL, HA, by simpa only [List.take_length, ← EO] using HH⟩
  · have HT := RP.forget.spine_cut_source_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) HTsource
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA pre.length
    exact .inr ⟨ls', pre, pending, target, cp, ct, hc, RP, HR, HN, RT,
      by simpa only [List.take_left] using HH⟩

/-- Taking a prefix of a completed source keeps the exact current scope.
This is the zero-step case of actual component preservation. -/
theorem EqTargetPrefixCompletion.take_prefix {D : Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending))) :
    EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) := by
  have HH := HP.compute_components heq hs hΓ (.rfl (fun _ _ => by rfl))
    (typed_const_levels_wf HP.prefix.typed)
    (show List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) (pre ++ pending) (pre ++ pending) from
      .rfl (fun _ _ => .refl)) pre.length
  simpa only [List.take_left] using HH

/-- In an actual first-beta decomposition, changing annotations and arguments
may be arbitrary. The exact lambda history either supplies a completed
post-beta spine, even beyond the target length, or its original-scope body path has a prefix-completed non-level
root. This derives the consumption branch from counted execution; no body
component-history hypothesis or target-image agreement is added. -/
theorem EqTargetPrefixCompletion.consumed_eta_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
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
      (EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∨
        TargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  have HPpre := HP.take_prefix heq hs hΓ
  have HPbody := HPpre.eta heq hs hΓ ht RN SD
  have HTpre : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) :=
    typed_spine_head (by simpa only [ProofShape.mkApps_append] using HTwhole)
  have HTfresh := native_eta_body_typed
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) HTpre RN SD
  obtain ⟨cd, cb, bodyStage, hc, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    HTpre (.intro RN SD) RF
  refine ⟨cd, cb, bodyStage, hc, RD, RB, ?_⟩
  have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
      ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
      ProofShape.mkApps]
  rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ HTfresh) (ES ▸ RB) with
    ⟨bodyLs, rawBody, EO, HL, HA, _⟩ | Hcut
  · have HTbody := EO ▸ HTfresh.pi_inert_compute heq hs RB.forget
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
theorem EqTargetPrefixCompletion.consumed_eta_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixCompletion Γ v w original Δ
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
    (EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∧
      cs+ck < cost ∧ PiInertTypedContinuationMinimum D Ω out Δ
        (ProofShape.mkApps (body'.inst x') rest') (cs+ck)) ∨
    (∃ cd cb bodyStage, cd+cb = cf ∧ cb < cost ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      TargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  obtain ⟨cd, cb, bodyStage, hc, RD, RB, Hnext | Hcut⟩ :=
    HP.consumed_eta_execution heq hs hΓ ht HTwhole RN SD RF RX
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


/-- Split the actual entire suffix of an eta expansion, with any pending
argument vector, including none. In the retained
case, endpoint completion moves into the actual changed annotation context;
a selected body root keeps its original binder context. In the consumed case,
completion is derived at the exact beta endpoint at every arity, or a prefix-completed body root is
selected. Both cases retain the actual lambda, argument and suffix paths and
their original count bound. The retained endpoint transfer is derived from
the actual annotation computation through each unused insertion. -/
theorem EqTargetPrefixCompletion.eta_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixCompletion Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pendingArgs)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pendingArgs)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.lam A
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) pendingArgs) endpoint) :
    (∃ A' body' args' cf ca cd cb bodyStage, cf+ca ≤ cost ∧ cd+cb = cf ∧
      endpoint = ProofShape.mkApps (.lam A' body') args' ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca pendingArgs args' ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (EqTargetPrefixCompletion Γ v w original (A' :: Δ) body' ∨
        TargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb)) ∨
    (∃ A' body' x' rest' cf ca cs cd cb bodyStage, cf+ca+cs ≤ cost ∧ cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca pendingArgs (x' :: rest') ∧
      ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') rest') endpoint ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∨
        TargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb)) := by
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', body', x', rest', cf, ca, cs, hc, RF, RX, RS⟩
  · have HPpre := HP.take_prefix heq hs hΓ
    have HPbody := HPpre.eta heq hs hΓ ht RN SD
    have HTpre : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) :=
      typed_spine_head (by simpa only [ProofShape.mkApps_append] using HTwhole)
    have HTfresh := native_eta_body_typed
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) HTpre RN SD
    obtain ⟨cd, cb, bodyStage, hcb, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
      HTpre (.intro RN SD) RF
    refine .inl ⟨A', body', args', cf, ca, cd, cb, bodyStage, hc, hcb, EO, RF, RX, RD, RB, ?_⟩
    have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
        ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
      simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
        ProofShape.mkApps]
    rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ HTfresh) (ES ▸ RB) with
      ⟨_, _, _, _, _, HPend⟩ | Hcut
    · exact .inl (HPend.compute_annotation (pi_inert_stage_certificate_descent heq hs n) hΓ RD.forget)
    · exact .inr (ES.symm ▸ Hcut)
  · cases pendingArgs with
    | nil => cases RX
    | cons x rest =>
      obtain ⟨cd, cb, bodyStage, hcb, RD, RB, Hbody⟩ :=
        HP.consumed_eta_execution heq hs hΓ ht HTwhole RN SD RF RX
      exact .inr ⟨A', body', x', rest', cf, ca, cs, cd, cb, bodyStage,
        hc, hcb, RF, RX, RS, RD, RB, Hbody⟩


/-- A selected native eta root yields a strictly smaller typed minimum whose
fresh source has the same bounded-prefix completion, at every source arity.
The continuation is the actual retained-or-consumed execution, and competitors
still range over all finite stages and endpoints. No target inhabitant is
introduced after the original vector is exhausted. Administrative roots and
component-only transitions through enclosing wrappers remain separate cases. -/
theorem EqTargetPrefixCompletion.eta_typed_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) pending) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ source endpoint' → K endpoint' k → cost ≤ j+k) :
    ∃ smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Ω out (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) smaller ∧
      EqTargetPrefixCompletion Γ v w original (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) := by
  obtain ⟨smaller, hsmall, HM⟩ := pi_inert_eta_typed_continuation_frames heq hs
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    HTwhole RN SD RP HR RT HK hcost hmin
  exact ⟨smaller, hsmall, HM, HP.eta heq hs hΓ ht RN SD⟩

end Lean4Lean.VEnv.Strengthening
