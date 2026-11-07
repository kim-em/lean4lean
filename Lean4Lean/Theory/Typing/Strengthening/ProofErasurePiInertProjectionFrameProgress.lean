import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedPairConsumption

/-! # Count projection frames through retained binder execution

Keep the selected observer and its exact typed substitution. Executing a
retained prefix rebuilds its binder frames over the actual suffix, omitting
the intervening application frame. The body is its literal substituted image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map lambda_body_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

/-- An actual projection run with its exact number of application and retained
frames. The terminal projection contributes its primitive cost and no frame. -/
inductive PiInertProjectionRunFrames (D : Definitions) (Ω : List ProofShape) (family : Name) (index : Nat) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Nat → Prop where
  | projection : TypedSource Ω e → TypedSource Ω (.proj family index e) →
      ScopedComputeCount (PiInertStage D n) ck Ω (.proj family index e) out →
      PiInertProjectionRunFrames D Ω family index out Ω
        (PiInertProjectionContinuation D Ω family index out) e ck 0
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertProjectionRunFrames D Ω family index out Θ K e' ck frames →
      PiInertProjectionRunFrames D Ω family index out Δ (PiInertApplicationContinuation D Θ τ args K) e (cs+ck) (frames+1)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertProjectionRunFrames D Ω family index out Δ K (ProofShape.mkApps (.lam A' body) args) ck frames →
      PiInertProjectionRunFrames D Ω family index out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck (frames+1)

/-- Forget only the number of selected frames. -/
theorem PiInertProjectionRunFrames.forget
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames) :
    PiInertProjectionContinuationRun D Ω family index out Δ K e ck := by
  induction H with
  | projection HT HP R => exact .projection HT HP R
  | application HT W HTnext R _ ih => exact .application HT W HTnext R ih
  | retained HT SD RD WI _ ih => exact .retained HT SD RD WI ih

/-- Every selected finite projection run has a frame count. -/
theorem PiInertProjectionContinuationRun.frame_count
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck) :
    ∃ frames, PiInertProjectionRunFrames D Ω family index out Δ K e ck frames := by
  induction H with
  | projection HT HP R => exact ⟨0, .projection HT HP R⟩
  | application HT W HTnext R _ ih =>
    obtain ⟨frames, HF⟩ := ih
    exact ⟨frames+1, .application HT W HTnext R HF⟩
  | retained HT SD RD WI _ ih =>
    obtain ⟨frames, HF⟩ := ih
    exact ⟨frames+1, .retained HT SD RD WI HF⟩

/-- Primitive-count minimality with the selected run's frame count. There is
no extra restriction on competitors and no secondary minimality assumption. -/
def PiInertProjectionFrameMinimum (D : Definitions) (Ω : List ProofShape) (family : Name) (index : Nat) (out : ProofShape)
    (Δ : List ProofShape) (source : ProofShape) (cost frames : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertProjectionRunFrames D Ω family index out Δ K endpoint ck frames ∧ cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- Erasing the frame count preserves the original unrestricted minimum. -/
theorem PiInertProjectionFrameMinimum.forget
    (H : PiInertProjectionFrameMinimum D Ω family index out Δ source cost frames) :
    PiInertProjectionContinuationMinimum D Ω family index out Δ source cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, R, HK.forget, hc, HM⟩

/-- Refine an existing minimum by counting its actual continuation frames. -/
theorem PiInertProjectionContinuationMinimum.frame_count
    (H : PiInertProjectionContinuationMinimum D Ω family index out Δ source cost) :
    ∃ frames, PiInertProjectionFrameMinimum D Ω family index out Δ source cost frames := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨frames, HF⟩ := HK.frame_count
  exact ⟨frames, K, n, cb, ck, endpoint, HT, R, HF, hc, HM⟩

/-- Read any selected typed lambda-spine minimum in its original body scope,
using exactly one frame over the selected outer tail. A surviving lambda keeps
its actual annotation path; a consumed lambda keeps its actual argument map
and post-beta suffix. Primitive cost does not increase, and all competitors
remain unrestricted. No completion or eta-origin premise is used. -/
theorem pi_inert_lambda_spine_body_projection_frame_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (R : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps (.lam A body) args) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K endpoint ck frames)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A body) args) tail → K tail k → ct+ck ≤ j+k) :
    ∃ smaller, smaller ≤ ct+ck ∧ PiInertProjectionFrameMinimum D Ω family index out (A :: Δ) body smaller (frames+1) := by
  have HTlam : TypedSource Δ (.lam A body) := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody A .hole).typed HTlam
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, rfl, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have hexact := HM _ _ _ ck (lambda_body_replace RD RB RX) HK.forget.holds
    refine ⟨cb+ck, by omega, (fun body k => K (ProofShape.mkApps (.lam A' body) args') k),
      m, cb, ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HK
    · intro later j tail k RJ HL
      have HB := HM _ _ _ k (lambda_body_replace RD RJ RX) HL
      omega
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have WI : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') := by
      intro Γ hΓ EΓ
      exact typed_lambda_argument_map heq hs HT RX hΓ EΓ
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam A' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
    have HTnext := HT.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
    have Ractual := ((lambda_body_replace RD RB RX).trans
      (Rbeta.mono (pi_inert_stage_mono (Nat.le_max_left n m)))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_left n m)))
    have hexact := HM _ _ _ ck Ractual HK.forget.holds
    refine ⟨cb+(cs+ck), by omega, PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · exact .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WI)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    · rintro later j tail k RJ ⟨suffixStage, tailCount, last, lastCost, hsum, RT, HL⟩
      have Rprefix := lambda_body_replace RD RJ RX
      have RBeta : ScopedComputeCount (PiInertStage D (max n later)) 0 Δ
          (ProofShape.mkApps (.lam A' tail) (x' :: xs')) (ProofShape.mkApps (tail.inst x') xs') := by
        simpa only [ProofShape.mkApps, Nat.zero_add] using
          (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
            (BetaRed.beta (A := A') (b := tail) (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
      have RT' : ScopedComputeCount (PiInertStage D suffixStage) tailCount Δ
          (ProofShape.mkApps (tail.inst x') xs') last := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RT
      have RR := ((Rprefix.trans RBeta).mono
        (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
        (RT'.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
      have HB := HM _ _ _ lastCost RR HL
      omega

/-- The same body readout applies to any frame-refined whole lambda minimum.
Only one frame is added to its actual tail, independently of path length. -/
theorem PiInertProjectionFrameMinimum.lambda_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertProjectionFrameMinimum D Ω family index out Δ (ProofShape.mkApps (.lam A body) args) cost frames) :
    ∃ smaller, smaller ≤ cost ∧ PiInertProjectionFrameMinimum D Ω family index out (A :: Δ) body smaller (frames+1) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨smaller, hsmall, Hbody⟩ := pi_inert_lambda_spine_body_projection_frame_minimum heq hs HT R HK
    (by simpa only [hc] using HM)
  exact ⟨smaller, by omega, Hbody⟩


end Lean4Lean.VEnv.Strengthening
