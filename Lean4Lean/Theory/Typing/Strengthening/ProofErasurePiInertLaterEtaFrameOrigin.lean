import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaFrameOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaBodyCut

/-! # Later retained eta execution with an arbitrary remaining continuation

Ordinary typed eta origin survives endpoint substitution. It suffices to read
both branches of a later lambda computation, without forcing immediate carrier
exposure or assuming that the original native recovery guard substitutes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private lambda_tail_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaBodyCut
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem retained_lambda_replace
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D later) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args') :
    ScopedComputeCount (PiInertStage D (max later n)) (cd+cb+ca) Δ
      (ProofShape.mkApps (.lam A body) args) (ProofShape.mkApps (.lam A' body') args') := by
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max later n) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_right later n)
  exact (ScopedComputeCount.lam (RD.mono raise)
    (RB.mono (pi_inert_stage_mono (Nat.le_max_left later n)))).mkApps (RX.mono raise)

/-- An actual typed eta origin yields both exact later frame branches from a
minimum with any fixed continuation. The larger budget accounts for earlier
work, giving strict decrease even if this later lambda is retained. No native
recovery certificate is needed at the current scope. -/
theorem TypedEtaOrigin.frame_origin_of_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HO : TypedEtaOrigin Δ A f u)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (HK : K endpoint ck) (hbudget : ct+ck < budget)
    (hmin : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint' →
      K endpoint' k → ct+ck ≤ j+k) :
    CountedEtaFrameOrigin D n Δ f A u args endpoint ct ck budget K := by
  have SD : DomainSort Δ A u := by
    obtain ⟨Γ, a, g, B, hΓ, EΓ, ha, _, _, EA, _⟩ := HO
    exact ⟨Γ, a, hΓ, EΓ, ha, EA⟩
  have HTbody : TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) :=
    (ScopedHole.lamBody A .hole).typed HO.lambda_typed
  refine ⟨SD, ?_⟩
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := HO.count_body_readout heq hs RF
    have hrev := hmin n (cf+ca) _ ck (RF.mkApps RX) (EO ▸ HK)
    have hexact : cd+cb+ca = ct := by omega
    refine .inl ⟨A', body', args', cf, ca, cd, cb, m, hc, hsplit, EO,
      RF, RX, RD, HTbody, RB, by omega, ?_⟩
    intro later j body k RJ HK'
    have HH := hmin _ _ _ _ (retained_lambda_replace RD RJ RX) HK'
    omega
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := HO.count_body_readout heq hs RF
    have hrev := hmin _ _ _ _ (lambda_tail_replace RD RB RX RS) HK
    have hexact : cd+cb+ca+cs = ct := by omega
    have WI : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') :=
      HO.body_interpretation heq hs (HO.shorten_spine HT) RX
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam A' body') (x' :: xs'))
        (ProofShape.mkApps (body'.inst x') xs') := by
      simpa only [ProofShape.mkApps] using
        (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
          (ScopedArgumentsCount.refl (args := xs'))
    have HTnext := HT.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
    refine .inr ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, hc, hsplit,
      RF, RX, RD, HTbody, RB, WI, HTnext, RS, by omega, ?_⟩
    rintro later j body k RJ ⟨tailStage, tailCost, tail, afterCost, hcost, RK, HK'⟩
    have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max n tailStage) Δ a b :=
      pi_inert_stage_mono (Nat.le_max_left n tailStage)
    have RK' : ScopedComputeCount (PiInertStage D (max n tailStage)) tailCost Δ
        (ProofShape.mkApps (body.inst x') xs') tail := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        RK.mono (pi_inert_stage_mono (Nat.le_max_right n tailStage))
    have HH := hmin _ _ _ _ (lambda_tail_replace (RD.mono raise) RJ (RX.mono raise) RK') HK'
    omega

/-- Following a retained eta endpoint through its next typed substitution and
application keeps both later branches and their exact argument origins. The
remaining typed continuation may contain more retained or application frames;
its current endpoint need not expose a carrier. Earlier positive work makes
the later child minimum strictly smaller than the original global budget. -/
theorem pi_inert_retained_eta_frame_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HO : TypedEtaOrigin Δ A short u)
    (RL : ScopedComputeCount (PiInertStage D firstStage) cl Δ original
      (ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args))
    (W : ContextSubstitution Δ Ξ τ)
    (HT : TypedSource Ξ (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args).subst τ) pending) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (hpositive : 0 < cl) (hcost : cl+ct+ck ≤ cost)
    (hmin : ∀ sourceStage tailStage j k body endpoint' l,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original body →
      ScopedComputeCount (PiInertStage D tailStage) k Ξ
        (ProofShape.mkApps (body.subst τ) pending) endpoint' → K endpoint' l → cost ≤ j+k+l) :
    CountedEtaFrameOrigin D n Ξ (short.subst τ) (A.subst τ) u
      (args.map (·.subst τ) ++ pending) endpoint ct ck cost K := by
  have HO' := HO.subst W
  have HT' : TypedSource Ξ
      (ProofShape.mkApps (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
        (args.map (·.subst τ) ++ pending)) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using HT
  have RT' : ScopedComputeCount (PiInertStage D n) ct Ξ
      (ProofShape.mkApps (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
        (args.map (·.subst τ) ++ pending)) endpoint := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using RT
  have hexact := hmin firstStage n cl ct _ endpoint ck RL RT HK.holds
  apply HO'.frame_origin_of_minimum heq hs HT' RT' HK.holds (by omega)
  intro later j endpoint' k RJ HK'
  have HH := hmin firstStage later cl j _ endpoint' k RL (by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using RJ) HK'
  omega

/-- Build the later frame origin directly from a native eta insertion and its
actual retained component computation. The insertion supplies the positive
cost required for strict descent; neither immediate carrier exposure nor
native recovery after substitution is an extra premise. This records one
later application, not a linked history through arbitrary intervening frames. -/
theorem pi_inert_native_retained_eta_frame_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (W : ContextSubstitution Δ Ξ τ)
    (HTlater : TypedSource Ξ (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A' (.app g (etaArgument u))) args').subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D suffixStage) ct Ξ (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A' (.app g (etaArgument u))) args').subst τ) pending) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (hcost : cp+1+cd+cg+ca+ct+ck ≤ cost)
    (hmin : ∀ sourceStage tailStage j k body endpoint' l,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original body →
      ScopedComputeCount (PiInertStage D tailStage) k Ξ
        (ProofShape.mkApps (body.subst τ) pending) endpoint' → K endpoint' l → cost ≤ j+k+l) :
    ∃ short, ScopedComputeCount (PiInertStage D m) cg Δ f short ∧
      g = short.liftN 1 ∧ TypedEtaOrigin Δ A' short u ∧
      CountedEtaFrameOrigin D suffixStage Ξ (short.subst τ) (A'.subst τ) u
        (args'.map (·.subst τ) ++ pending) endpoint ct ck cost K := by
  obtain ⟨short, RF, EG, HO⟩ := pi_inert_retained_eta_origin
    heq hs hguard (typed_spine_head HT) RN SD RD RG
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max m n) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_right m n)
  have RB := (RG.mono (pi_inert_stage_mono (Nat.le_max_left m n))).app
    (ScopedComputeCount.beta (BetaRed.refl (e := etaArgument u)))
  have Rlam := (ScopedComputeCount.base (raise HR)).trans
    (ScopedComputeCount.lam (RD.mono raise) RB)
  have RL : ScopedComputeCount (PiInertStage D (max m n)) (cp+1+cd+cg+ca) Δ original
      (ProofShape.mkApps (.lam A' (.app (short.liftN 1) (etaArgument u))) args') := by
    simpa only [EG, Nat.add_zero, Nat.add_assoc] using
      (RP.mono raise).trans (Rlam.mkApps (RX.mono raise))
  refine ⟨short, RF, EG, HO, ?_⟩
  exact pi_inert_retained_eta_frame_origin heq hs HO RL W
    (by simpa only [EG] using HTlater) (by simpa only [EG] using RT) HK
    (by omega) hcost hmin

end Lean4Lean.VEnv.Strengthening
