import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConsumedBodyRoot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedEtaOrigin

/-! # Minimum eta bodies with an arbitrary fixed continuation

Application and retained-lambda frames can be prepended to a continuation
without substituting any computation. In both cases the body and its fixed
continuation have a strictly smaller minimum. Bypassing administrative body
histories through these more general frames remains a separate obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

/-- A fixed endpoint substitution and argument spine, followed by a counted
computation and an arbitrary fixed continuation. Only the endpoint is substituted.
Repeated application of this definition represents arbitrarily many frames. -/
def PiInertApplicationContinuation (D : Definitions) (Δ : List ProofShape)
    (τ : ProofShape.Subst) (pending : List ProofShape)
    (K : ProofShape → Nat → Prop) (body : ProofShape) (cost : Nat) : Prop :=
  ∃ n cs endpoint ck, cs+ck = cost ∧
    ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body.subst τ) pending) endpoint ∧ K endpoint ck

/-- Consuming a lambda produces a strictly smaller minimum for its body plus
the new application frame and all enclosing continuation frames. Competitors
may change every intermediate endpoint, count, and finite guard stage while
keeping the continuation predicate fixed. No guarded substitution is used. -/
theorem pi_inert_counted_lambda_continuation_minimal_of
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A body))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out)
    (HK : K out ck)
    (hcost : cp+1+cd+cb+ca+cs+ck ≤ cost)
    (hmin : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → cost ≤ j+k) :
    cp+1+cd+cb+ca+cs+ck = cost ∧ cb+cs+ck < cost ∧
      ∀ later j endpoint k,
        ScopedComputeCount (PiInertStage D later) j (A :: Δ) body endpoint →
        PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K endpoint k →
        cb+cs+ck ≤ j+k := by
  have HM := hmin _ _ _ _ (pi_inert_counted_lambda_body_replace RP HR RD RB RX RS) HK
  refine ⟨by omega, by omega, ?_⟩
  rintro later j endpoint k RJ ⟨suffixStage, cs', out', ck', hsplit, RS', HK'⟩
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max n suffixStage) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_left n suffixStage)
  have RS'' : ScopedComputeCount (PiInertStage D (max n suffixStage)) cs' Δ
      (ProofShape.mkApps (endpoint.inst x') xs') out' := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RS'.mono (pi_inert_stage_mono (Nat.le_max_right n suffixStage))
  have RR := pi_inert_counted_lambda_body_replace (RP.mono raise) (raise HR)
    (RD.mono raise) RJ (RX.mono raise) RS''
  have HM' := hmin _ _ _ _ RR HK'
  omega

/-- When the lambda survives the current scope, retain it as a fixed frame
around the variable body endpoint. This also gives a strictly smaller minimum;
no application or substitution of that body path is needed. -/
theorem pi_inert_retained_lambda_continuation_minimal_of
    {K : ProofShape → Nat → Prop}
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A body))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args')
    (HK : K (ProofShape.mkApps (.lam A' body') args') ck)
    (hcost : cp+1+cd+cb+ca+ck ≤ cost)
    (hmin : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → cost ≤ j+k) :
    cp+1+cd+cb+ca+ck = cost ∧ cb+ck < cost ∧
      ∀ later j endpoint k,
        ScopedComputeCount (PiInertStage D later) j (A :: Δ) body endpoint →
        K (ProofShape.mkApps (.lam A' endpoint) args') k → cb+ck ≤ j+k := by
  have replace : ∀ {later j endpoint},
      ScopedComputeCount (PiInertStage D later) j (A :: Δ) body endpoint →
      ScopedComputeCount (PiInertStage D (max later n)) (cp+1+cd+j+ca) Δ
        original (ProofShape.mkApps (.lam A' endpoint) args') := by
    intro later j endpoint RJ
    have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max later n) Δ a b :=
      pi_inert_stage_mono (Nat.le_max_right later n)
    have RF := (ScopedComputeCount.base (raise HR)).trans
      (ScopedComputeCount.lam (RD.mono raise) (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later n))))
    simpa only [Nat.add_assoc] using (RP.mono raise).trans (RF.mkApps (RX.mono raise))
  have HM := hmin _ _ _ _ (replace RB) HK
  refine ⟨by omega, by omega, ?_⟩
  intro later j endpoint k RJ HK'
  have HM' := hmin _ _ _ _ (replace RJ) HK'
  omega

/-- An eta yields a typed body with a strictly smaller combined minimum.
If its lambda survives, the new continuation retains that lambda; if it is
consumed, the new frame carries the actual argument's typed substitution.
In the surviving case, a component-only body retains the counted short-function
path and its actual Pi typing at the changed annotation.
For a constant-headed source, the consumed case also retains an exact counted
non-level body root; component-only computation is bypassed before the continuation.
No carrier exposure of the intermediate body endpoint is asserted. -/
def CountedEtaContinuationCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (f A : ProofShape) (u : VLevel) (args : List ProofShape) (out : ProofShape)
    (ct ck cost : Nat) (K : ProofShape → Nat → Prop) : Prop :=
  DomainSort Δ A u ∧ (
  (∃ A' body' args' cf ca, cf+ca ≤ ct ∧
    out = ProofShape.mkApps (.lam A' body') args' ∧
    ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app (f.liftN 1) (etaArgument u))) (.lam A' body') ∧
    ScopedArgumentsCount (PiInertStage D n) Δ ca args args' ∧ K out ck ∧
    ∃ cd cb m, cd+cb = cf ∧ cb+ck < cost ∧
      TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      (∀ g cg, ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g →
        body' = .app g (etaArgument u) →
        ∃ short, ScopedComputeCount (PiInertStage D m) cg Δ f short ∧
          body' = .app (short.liftN 1) (etaArgument u) ∧ TypedEtaOrigin Δ A' short u) ∧
      ∀ later j endpoint k,
        ScopedComputeCount (PiInertStage D later) j (A :: Δ)
          (.app (f.liftN 1) (etaArgument u)) endpoint →
        K (ProofShape.mkApps (.lam A' endpoint) args') k → cb+ck ≤ j+k) ∨
  (∃ body' x' xs' cb cs m,
    cb+cs+ck < cost ∧
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
    ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body' ∧
    ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out ∧ K out ck ∧
    (∀ c ls pre, f = ProofShape.mkApps (.const c ls) pre →
      CountedNonlevelSpineRoot D m (A :: Δ) c ls (pre.map (·.liftN 1) ++ [etaArgument u]) body' cb) ∧
    ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) endpoint →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K endpoint k →
      cb+cs+ck ≤ j+k))

/-- The minimum-count induction step for an eta with any fixed continuation.
Both the consumed and retained lambda cases yield smaller body minima. These
frames can be nested without transporting any guarded computation by substitution. -/
theorem pi_inert_eta_continuation_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) out)
    (HK : K out ck) (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → cost ≤ j+k) :
    CountedEtaContinuationCut D n Δ f A u args out ct ck cost K := by
  refine ⟨SD, ?_⟩
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    obtain ⟨_, hsmall, HM⟩ := pi_inert_retained_lambda_continuation_minimal_of
      RP HR RD RB RX (EO ▸ HK) (by omega) hmin
    have HTbody : TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) := by
      obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := typed_spine_head HT
      obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
        hΓ ht EΓ Ee (ScopedCompute.base HR)
      exact (ScopedHole.lamBody A .hole).typed ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩
    refine .inl ⟨A', body', args', cf, ca, hc, EO, RF, RX, HK,
      cd, cb, m, hsplit, hsmall, HTbody, RD, RB, ?_, HM⟩
    intro g cg RG EB
    obtain ⟨short, RS, EG, HO⟩ := pi_inert_retained_eta_origin
      heq hs hguard (typed_spine_head HT) RN SD RD RG
    exact ⟨short, RS, by simpa only [EG] using EB, HO⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    obtain ⟨_, hsmall, HM⟩ := pi_inert_counted_lambda_continuation_minimal_of
      RP HR RD RB RX RS HK (by omega) hmin
    obtain ⟨HTbody, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
    refine .inr ⟨body', x', xs', cb, cs, m, hsmall, HTbody, WI, RB, RS, HK, ?_, HM⟩
    rintro c ls pre rfl
    apply pi_inert_eta_body_spine_root heq hs HTbody RB
    · intro later j RJ
      have HK' : PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K body' (cs+ck) :=
        ⟨n, cs, out, ck, rfl, by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS, HK⟩
      have HJ := HM later j body' (cs+ck) RJ HK'
      omega
    · intro g cg hcg RG EB
      have RR := pi_inert_retained_eta_body_count_bypass heq hs hguard HT RN SD RG RX (EB ▸ RS)
      have RP' := RP.mono (pi_inert_stage_mono (Nat.le_max_right m n))
      have HB := hmin _ _ _ _ (RP'.trans RR) HK
      omega

/-- Apply the continuation induction step to the actual inner eta selected
by the Eq-exposure cut. Its enclosing beta frame is fixed, and the combined
body/suffix minimum is strictly smaller than the original whole-path count.
The resulting smaller body minimum retains either a lambda or an application
frame, according to whether the inner lambda was consumed in its own scope. -/
theorem CountedEtaBodySpineCut.nested_eta_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct (EqEtaRemainingRoot D))
    (hcost : cp+1+ct ≤ cost) :
    ∃ cb cs m ls' bodyPre bodyPending innerA innerU body' x' xs' tb,
      cb+cs < cost ∧
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
      ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') out ∧
      CountedEtaContinuationCut D m (A :: Δ) (ProofShape.mkApps (.const ``Eq.rec ls') bodyPre)
        innerA innerU bodyPending body' tb cs (cb+cs)
        (fun endpoint k => ∃ later, ScopedComputeCount (PiInertStage D later) k Δ
          (ProofShape.mkApps (endpoint.inst x') xs') out) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, _, RX, RS, _, _, _, RP, HR, _, RT, _, HM, _, _, WI, _, k, _, HEta⟩ := H
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have HTwhole : TypedSource (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls') bodyPre) bodyPending) := by
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTbody
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs m))
      hΓ ht EΓ Ee RP.forget
    exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, by simpa only [ProofShape.mkApps_append] using EE⟩
  cases HEta with
  | @intro innerA innerB innerU RNinner SDinner =>
    refine ⟨cb, cs, m, ls', bodyPre, bodyPending, innerA, innerU, body', x', xs', tb,
      by omega, WI, RS, ?_⟩
    apply pi_inert_eta_continuation_cut heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RNinner SDinner
      (by simpa only [ProofShape.mkApps_append] using RP) HR RT ⟨n, RS⟩ (by omega)
    rintro later j endpoint suffixCost RJ ⟨suffixStage, RK⟩
    exact HM later suffixStage j suffixCost endpoint RJ RK

end Lean4Lean.VEnv.Strengthening
