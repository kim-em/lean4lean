import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedEtaContinuation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertContinuationFrames

/-! # Extract the body cut at later consumption of a retained eta

An exposed final output forces the retained lambda to be consumed after the
endpoint substitution. Joint minimality across the two scopes gives exact
counts and a smaller body/suffix minimum. If the retained short function is
constant-headed, the two-scope bypass forces a non-level root in this body.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem lambda_tail_replace
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D later) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out) :
    ScopedComputeCount (PiInertStage D (max later n)) (cd+cb+ca+cs) Δ
      (ProofShape.mkApps (.lam A body) args) out := by
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max later n) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_right later n)
  have RF := ScopedComputeCount.lam (RD.mono raise)
    (RB.mono (pi_inert_stage_mono (Nat.le_max_left later n)))
  have Rbeta : ScopedComputeCount (PiInertStage D (max later n)) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs'))
      (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  simpa only [Nat.zero_add] using
    (RF.mkApps (RX.mono raise)).trans (Rbeta.trans (RS.mono raise))

/-- The actual later beta decomposition, with exact counts, a smaller joint
body/suffix minimum, and a typed non-level root whenever its short function
is constant-headed. This is a proved decomposition, not a closure assumption.
The optional root predicate refines the same selected witness. By default,
the non-level root still needs classification and elimination. -/
def CountedLaterEtaBodyCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (A f : ProofShape) (u : VLevel) (args : List ProofShape) (out : ProofShape)
    (ct cost : Nat)
    (Root : Nat → List ProofShape → ProofShape → ProofShape → Prop := fun _ _ _ _ => True) : Prop :=
  ∃ A' body' x' xs' cd cb ca cs m,
    cd+cb+ca+cs = ct ∧ cb+cs < cost ∧
    ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
    ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body' ∧
    ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
    ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') out ∧
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
    (∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Δ
        (ProofShape.mkApps (endpoint.inst x') xs') out → cb+cs ≤ j+k) ∧
    (∀ c ls pre, f = ProofShape.mkApps (.const c ls) pre →
      CountedNonlevelSpineRoot D m (A :: Δ) c ls
        (pre.map (·.liftN 1) ++ [etaArgument u]) body' cb Root)

/-- The extracted later body has a smaller concrete continuation minimum
ending at the original exposed output. Its actual first argument supplies
the typed instantiation frame; no native image recovery is required. -/
theorem CountedLaterEtaBodyCut.frames
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (H : CountedLaterEtaBodyCut D n Δ A f u args out ct cost Root) :
    ∃ smaller, smaller < cost ∧ PiInertContinuationMinimum D Δ out (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨A', body', x', xs', cd, cb, ca, cs, m, _, hsmall, _, RB, _, RS, HT, WI, HM, _⟩ := H
  refine ⟨cb+cs, hsmall,
    (fun endpoint k => ∃ later, ScopedComputeCount (PiInertStage D later) k Δ
      (ProofShape.mkApps (endpoint.inst x') xs') out), m, cb, cs, body',
    PiInertContinuationFrames.inst WI, HT, RB, ⟨n, RS⟩, rfl, ?_⟩
  rintro later j endpoint k RJ ⟨suffixStage, RK⟩
  exact HM later suffixStage j k endpoint RJ RK

/-- Extract the later-consumption decomposition from the actual continuation
path. The retained long endpoint has a counted first-scope path; its short
alternative saves at least one occurrence there. Global two-scope minimality
then forces an exact, smaller later body/suffix minimum and excludes a merely
retained fresh slot. Only the endpoint and ordinary typing are substituted.
The final output must expose a carrier; additional retained frames are still
outside this theorem's conclusion. -/
theorem pi_inert_retained_eta_later_body_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedEtaOrigin Δ A short u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (RF : ScopedComputeCount (PiInertStage D m) cf Δ f short)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (RL : ScopedComputeCount (PiInertStage D firstStage) cl Δ original
      (ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args'))
    (W : ContextSubstitution Δ Ω τ)
    (HT : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args').subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D suffixStage) ct Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A (.app (short.liftN 1) (etaArgument u))) args').subst τ) pending) out)
    (HE : CarrierExposure out)
    (hsave : cp+1+cf+ca ≤ cl) (hcost : cl+ct ≤ cost)
    (hmin : ∀ sourceStage tailStage j k endpoint,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original endpoint →
      ScopedComputeCount (PiInertStage D tailStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cost ≤ j+k) :
    CountedLaterEtaBodyCut D suffixStage Ω (A.subst τ) (short.subst τ) u
      (args'.map (·.subst τ) ++ pending) out ct cost := by
  have HO := H.subst W
  have HTlong : TypedSource Ω
      (ProofShape.mkApps (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
        (args'.map (·.subst τ) ++ pending)) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using HT
  have RT' : ScopedComputeCount (PiInertStage D suffixStage) ct Ω
      (ProofShape.mkApps (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
        (args'.map (·.subst τ) ++ pending)) out := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
      ProofShape.etaArgument_subst, ProofShape.mkApps_append] using RT
  have htail : ∀ later k, ScopedComputeCount (PiInertStage D later) k Ω
      (ProofShape.mkApps (.lam (A.subst τ) (.app ((short.subst τ).liftN 1) (etaArgument u)))
        (args'.map (·.subst τ) ++ pending)) out → ct ≤ k := by
    intro later k RK
    have HM := hmin firstStage later cl k _ RL (by
      simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.lift_subst_lift,
        ProofShape.etaArgument_subst, ProofShape.mkApps_append] using RK)
    omega
  rcases RT'.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args'', cfun, cargs, _, EO, _, _⟩ |
    ⟨A', body', x', xs', cfun, cargs, cs, hc, Rfun, Rargs, RS⟩
  · exact (HE.not_lambda_spine A' body' args'' EO).elim
  obtain ⟨cd, cb, bodyStage, hsplit, RD, RB⟩ := HO.count_body_readout heq hs Rfun
  have hexact : cd+cb+cargs+cs = ct := by
    have HM := htail _ _ (lambda_tail_replace RD RB Rargs RS)
    omega
  have HMbody : ∀ later tailStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j (A.subst τ :: Ω)
        (.app ((short.subst τ).liftN 1) (etaArgument u)) endpoint →
      ScopedComputeCount (PiInertStage D tailStage) k Ω
        (ProofShape.mkApps (endpoint.inst x') xs') out → cb+cs ≤ j+k := by
    intro later tailStage j k endpoint RJ RK
    have raise : ∀ {Δ a b}, PiInertStage D suffixStage Δ a b →
        PiInertStage D (max suffixStage tailStage) Δ a b :=
      pi_inert_stage_mono (Nat.le_max_left suffixStage tailStage)
    have RR := lambda_tail_replace (RD.mono raise) RJ (Rargs.mono raise)
      (RK.mono (pi_inert_stage_mono (Nat.le_max_right suffixStage tailStage)))
    have HM := htail _ _ RR
    omega
  have HTbody : TypedSource (A.subst τ :: Ω)
      (.app ((short.subst τ).liftN 1) (etaArgument u)) :=
    (ScopedHole.lamBody (A.subst τ) .hole).typed HO.lambda_typed
  have WI : ContextSubstitution (A.subst τ :: Ω) Ω (ProofShape.Subst.one x') :=
    HO.body_interpretation heq hs (HO.shorten_spine HTlong) Rargs
  refine ⟨A', body', x', xs', cd, cb, cargs, cs, bodyStage, hexact,
    by omega, RD, RB, Rargs, RS, HTbody, WI, HMbody, ?_⟩
  intro c ls pre Eshort
  have hfixed : ∀ later j, ScopedComputeCount (PiInertStage D later) j (A.subst τ :: Ω)
      (.app ((short.subst τ).liftN 1) (etaArgument u)) body' → cb ≤ j := by
    intro later j RJ
    have HM := HMbody later suffixStage j cs body' RJ RS
    omega
  have hretain : ∀ g cg, cg ≤ cb →
      ScopedComputeCount (PiInertStage D bodyStage) cg (A.subst τ :: Ω)
        ((short.subst τ).liftN 1) g → body' = .app g (etaArgument u) → False := by
    intro g cg hcg RG EB
    obtain ⟨Rshort, Rtail⟩ := pi_inert_retained_eta_two_scope_bypass
      heq hs H RF RX W HT RG Rargs (EB ▸ RS)
    have RP' := RP.mono (pi_inert_stage_mono (Nat.le_max_right m n))
    have HM := hmin _ _ _ _ _ (RP'.trans Rshort) Rtail
    omega
  exact pi_inert_eta_body_spine_root heq hs (Eshort ▸ HTbody) (Eshort ▸ RB)
    (Eshort ▸ hfixed) (Eshort ▸ hretain)

/-- The original native eta, annotation path and component-only body supply
both first-scope alternatives and their cost difference. The actual later
path then yields the extracted body cut; no later beta decomposition, short
function representative, or separate cost-saving premise is assumed. The
returned short path and typed origin retain their connection to the original
source. Classification of the later non-level root remains open. -/
theorem pi_inert_native_retained_eta_later_body_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (W : ContextSubstitution Δ Ω τ)
    (HTlater : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A' (.app g (etaArgument u))) args').subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D suffixStage) ct Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.lam A' (.app g (etaArgument u))) args').subst τ) pending) out)
    (HE : CarrierExposure out)
    (hcost : cp+1+cd+cg+ca+ct ≤ cost)
    (hmin : ∀ sourceStage tailStage j k endpoint,
      ScopedComputeCount (PiInertStage D sourceStage) j Δ original endpoint →
      ScopedComputeCount (PiInertStage D tailStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cost ≤ j+k) :
    ∃ short, ScopedComputeCount (PiInertStage D m) cg Δ f short ∧
      g = short.liftN 1 ∧ TypedEtaOrigin Δ A' short u ∧
      CountedLaterEtaBodyCut D suffixStage Ω (A'.subst τ) (short.subst τ) u
        (args'.map (·.subst τ) ++ pending) out ct cost := by
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
  exact pi_inert_retained_eta_later_body_cut heq hs HO RP RF RX RL W
    (by simpa only [EG] using HTlater) (by simpa only [EG] using RT) HE
    (by omega) hcost hmin

end Lean4Lean.VEnv.Strengthening
