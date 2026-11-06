import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertNestedEtaMinimum

/-! # Retained eta bypass across an application continuation

The short function and arguments compute in the first scope. Only their
endpoint is substituted. A component-only body at later consumption can be
bypassed in the second scope, preserving its exact output and any remaining
continuation. The combined count saves the original eta occurrence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem erase_spine_inv (E : proofErase Γ e = ProofShape.mkApps f args) :
    ∃ f₀ args₀, e = VExpr.mkApps f₀ args₀ ∧ proofErase Γ f₀ = f ∧
      args₀.map (proofErase Γ) = args := by
  induction args using List.snoc_induction generalizing e with
  | nil => exact ⟨e, [], rfl, E, rfl⟩
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at E
    obtain ⟨g, y, rfl, _, Eg, Ey⟩ := erase_app_inv E
    obtain ⟨f₀, args₀, rfl, Ef, EA⟩ := ih Eg
    exact ⟨f₀, args₀ ++ [y], (VExpr.mkApps_snoc ..).symm, Ef,
      by simp only [List.map_append, List.map_cons, List.map_nil, EA, Ey]⟩

/-- A typed application spine of the retained eta lambda supplies typing for
the entire short spine with exactly the same arguments. This includes pending
arguments introduced only after a continuation's endpoint substitution. -/
theorem TypedEtaOrigin.shorten_spine (H : TypedEtaOrigin Δ A f u)
    (HT : TypedSource Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args)) :
    TypedSource Δ (ProofShape.mkApps f args) := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨long, actualArgs, rfl, EL, Eargs⟩ := erase_spine_inv Ee
  obtain ⟨a, g, B, ha, hg, hn, Ea, Eg⟩ := H.realize hΓ
  have hnl : ¬ IsProof Γ (.lam a (.app g.lift (.bvar 0))) :=
    fun hp => hn ((isProof_congr hΓ (IsDefEq.eta hg)).1 hp)
  have EE : proofErase Γ (.lam a (.app g.lift (.bvar 0))) =
      .lam A (.app (f.liftN 1) (etaArgument u)) := by
    rw [show proofErase Γ (.lam a (.app g.lift (.bvar 0))) =
      .lam (proofErase Γ a) (proofErase (a :: Γ) (.app g.lift (.bvar 0))) from if_neg hnl,
      proofErase_eta_body hΓ ha hg hn, Ea, Eg]
  obtain ⟨S, hlong⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ (IsDefEq.eta hg).hasType.1 hlong
    (EE.trans EL.symm)).2 hnl
  have HC := (HE.defeq hΓ).symm.trans henv hΓ (IsDefEq.eta hg).toU
  have HH := (HC.mkApps_congr_left henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
  have hp : ¬ IsProof Γ (VExpr.mkApps long actualArgs) := by
    intro hp
    have E := Ee.symm.trans (proofErase_eq_proof.2 hp)
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args x => rw [ProofShape.mkApps_snoc] at E; cases E
  have hp' := mt (isProof_congr hΓ HH).2 hp
  refine ⟨Γ, VExpr.mkApps g actualArgs, T, hΓ, rfl, HH.hasType.2, ?_⟩
  rw [proofErase_mkApps hΓ HH.hasType.2 hp', Eg, Eargs]

/-- The two sides of the substitution boundary keep separate counted paths.
The first path computes the short function and original arguments. The second
replays only computations made in the later scope and reaches the exact old
output. No guarded path is transported along the endpoint substitution. -/
theorem pi_inert_retained_eta_two_scope_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedEtaOrigin Δ A short u)
    (RF : ScopedComputeCount (PiInertStage D m) cf Δ f short)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (W : ContextSubstitution Δ Ω τ)
    (HT : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args').subst τ) pending))
    (RG : ScopedComputeCount (PiInertStage D later) cg (A.subst τ :: Ω)
      ((short.subst τ).liftN 1) g)
    (RY : ScopedArgumentsCount (PiInertStage D suffixStage) Ω cy
      (args'.map (·.subst τ) ++ pending) (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D suffixStage) cs Ω
      (ProofShape.mkApps ((ProofShape.app g (etaArgument u)).inst x') xs') out) :
    ScopedComputeCount (PiInertStage D (max m n)) (cf+ca) Δ
      (ProofShape.mkApps f args) (ProofShape.mkApps short args') ∧
    ScopedComputeCount (PiInertStage D (max later suffixStage)) (cg+cy+cs) Ω
      (ProofShape.mkApps ((ProofShape.mkApps short args').subst τ) pending) out := by
  refine ⟨(RF.mono (pi_inert_stage_mono (Nat.le_max_left m n))).mkApps
    (RX.mono (pi_inert_stage_mono (Nat.le_max_right m n))), ?_⟩
  have HO := H.subst W
  have HTlong : TypedSource Ω (ProofShape.mkApps
      (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
      (args'.map (·.subst τ) ++ pending)) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using HT
  have R := HO.component_body_bypass heq hs (HO.shorten_spine HTlong) RG RY RS
  simpa only [ProofShape.subst_mkApps, ProofShape.mkApps_append] using R

/-- In a minimum with an application continuation, an eta cannot retain a
component-only body in the first scope and again at its later consumption.
The two short paths preserve the later output and its arbitrary remaining
continuation, while the removed eta occurrence makes their total cheaper.
Annotation costs can be omitted from the bound because they are nonnegative. -/
theorem pi_inert_two_scope_minimum_no_retained_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedEtaOrigin Δ A short u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (RF : ScopedComputeCount (PiInertStage D m) cf Δ f short)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (W : ContextSubstitution Δ Ω τ)
    (HT : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args').subst τ) pending))
    (RG : ScopedComputeCount (PiInertStage D later) cg (A.subst τ :: Ω)
      ((short.subst τ).liftN 1) g)
    (RY : ScopedArgumentsCount (PiInertStage D suffixStage) Ω cy
      (args'.map (·.subst τ) ++ pending) (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D suffixStage) cs Ω
      (ProofShape.mkApps ((ProofShape.app g (etaArgument u)).inst x') xs') out)
    (HK : K out ck)
    (hcost : cp+1+cf+ca+cg+cy+cs+ck ≤ cost)
    (hmin : ∀ sourceStage j endpoint k,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original endpoint →
      PiInertApplicationContinuation D Ω τ pending K endpoint k → cost ≤ j+k) : False := by
  obtain ⟨RL, RR⟩ := pi_inert_retained_eta_two_scope_bypass heq hs H RF RX W HT RG RY RS
  have RP' := RP.mono (pi_inert_stage_mono (Nat.le_max_right m n))
  have HK' : PiInertApplicationContinuation D Ω τ pending K
      (ProofShape.mkApps short args') (cg+cy+cs+ck) :=
    ⟨max later suffixStage, cg+cy+cs, out, ck, rfl, RR, HK⟩
  have HM := hmin _ _ _ _ (RP'.trans RL) HK'
  omega

/-- Apply the two-scope contradiction directly to the original native eta
and its retained annotation/function histories. The typed origin and counted
short path are derived, not supplied as additional hypotheses. Thus a retained
eta in a minimum application continuation must leave the component-only form
before its later consumption. Other intervening retained frames are not yet
handled by this theorem. -/
theorem pi_inert_native_eta_two_scope_minimum_no_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (W : ContextSubstitution Δ Ω τ)
    (HTlater : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A' (.app g (etaArgument u))) args').subst τ) pending))
    (RG' : ScopedComputeCount (PiInertStage D later) cg' (A'.subst τ :: Ω)
      (g.subst τ.lift) g')
    (RY : ScopedArgumentsCount (PiInertStage D suffixStage) Ω cy
      (args'.map (·.subst τ) ++ pending) (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D suffixStage) cs Ω
      (ProofShape.mkApps ((ProofShape.app g' (etaArgument u)).inst x') xs') out)
    (HK : K out ck)
    (hcost : cp+1+cd+cg+ca+cg'+cy+cs+ck ≤ cost)
    (hmin : ∀ sourceStage j endpoint k,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original endpoint →
      PiInertApplicationContinuation D Ω τ pending K endpoint k → cost ≤ j+k) : False := by
  obtain ⟨short, RF, EG, HO⟩ := pi_inert_retained_eta_origin
    heq hs hguard (typed_spine_head HT) RN SD RD RG
  apply pi_inert_two_scope_minimum_no_retained_components heq hs HO RP RF RX W
    (by simpa only [EG] using HTlater)
    (by simpa only [EG, ProofShape.lift_subst_lift] using RG') RY RS HK (by omega) hmin

end Lean4Lean.VEnv.Strengthening
