import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameProgress

/-! # Execute a retained lambda without rebuilding its enclosing frames

A whole lambda-spine path reads back to its original body scope. Its actual
suffix is represented by one retained or consumed frame over the original
tail. This removes an enclosing retained/application pair at equal cost.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv erase_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem typed_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (.lam A body))
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.lam A body) (.lam A' body')) :
    ∃ u cd cb m, DomainSort Δ A u ∧ cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body' := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨a, b, rfl, _, EA, EB⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, ha⟩, B, hb⟩ := ht.lam_inv henv hΓ
  obtain ⟨a', b', cd, cb, m, hc, _, _, EO, RD, RB⟩ := pi_inert_lambda_count_readout
    heq hs hΓ ha hb rfl (by simpa only [EA, EB] using RF)
  obtain ⟨EA', EB'⟩ := ProofShape.lam.inj EO
  exact ⟨u, cd, cb, m, ⟨Γ, a, hΓ, rfl, ha, EA⟩, hc,
    by simpa only [EA, ← EA'] using RD,
    by simpa only [proofEraseCtx, EA, EB, ← EB'] using RB⟩

private theorem typed_lambda_argument_map
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs')) :
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') := by
  cases RX with
  | cons RX _ =>
    have HTapp : TypedSource Δ (.app (.lam A body) _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨A₀, B₀, hf, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨a, b, rfl, _, EA, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, ha⟩, B, hb⟩ := hf.lam_inv henv hΓ
    have hf' := HasType.lam ha hb
    have hxA := argument_at_displayed_domain hΓ hf hf' hx
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hxA rfl Ex RX.forget
    have hΓA : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
    have WI : ContextSubstitution (proofEraseCtx (a :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ x₁)) :=
      ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA HX.hasType.2)
        (erasedSubstAgreement_one hΓA HX.hasType.2)
    rw [proofEraseCtx, EA, EX] at WI
    intro Γ' hΓ' EΓ'
    exact WI hΓ' EΓ'

private theorem lambda_body_replace
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args args') :
    ScopedComputeCount (PiInertStage D (max n m)) (cd+cb+ca) Δ
      (ProofShape.mkApps (.lam A body) args) (ProofShape.mkApps (.lam A' body') args') :=
  ((RD.mono (pi_inert_stage_mono (Nat.le_max_left n m))).lam
    (RB.mono (pi_inert_stage_mono (Nat.le_max_right n m)))).mkApps
      (RX.mono (pi_inert_stage_mono (Nat.le_max_left n m)))

/-- Read any selected typed lambda-spine minimum in its original body scope,
using exactly one frame over the selected outer tail. A surviving lambda keeps
its actual annotation path; a consumed lambda keeps its actual argument map
and post-beta suffix. Primitive cost does not increase, and all competitors
remain unrestricted. No completion or eta-origin premise is used. -/
theorem pi_inert_lambda_spine_body_frame_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (R : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps (.lam A body) args) endpoint)
    (HK : PiInertRunFrames D Ω out Δ K endpoint ck frames)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A body) args) tail → K tail k → ct+ck ≤ j+k) :
    ∃ smaller, smaller ≤ ct+ck ∧ PiInertFrameMinimum D Ω out (A :: Δ) body smaller (frames+1) := by
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
theorem PiInertFrameMinimum.lambda_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertFrameMinimum D Ω out Δ (ProofShape.mkApps (.lam A body) args) cost frames) :
    ∃ smaller, smaller ≤ cost ∧ PiInertFrameMinimum D Ω out (A :: Δ) body smaller (frames+1) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨smaller, hsmall, Hbody⟩ := pi_inert_lambda_spine_body_frame_minimum heq hs HT R HK
    (by simpa only [hc] using HM)
  exact ⟨smaller, by omega, Hbody⟩

/-- A retained prefix with the exact number of selected lambda frames.
The annotations and argument vectors are the same as in the original prefix. -/
inductive PiInertRetainedPrefixCount (D : Definitions) :
    List ProofShape → List ProofShape → (ProofShape → ProofShape) → Nat → Prop where
  | refl : PiInertRetainedPrefixCount D Δ Δ id 0
  | retained : DomainSort Δ A u → ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertRetainedPrefixCount D Δ Θ plug depth →
      PiInertRetainedPrefixCount D (A :: Δ) Θ
        (fun e => plug (ProofShape.mkApps (.lam A' e) args)) (depth+1)

/-- Forget just the retained-prefix length. -/
theorem PiInertRetainedPrefixCount.forget
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) : PiInertRetainedPrefix D Δ Θ plug := by
  induction H with
  | refl => exact .refl
  | retained SD RD WI _ ih => exact .retained SD RD WI ih

/-- Expose the first actual application with the exact preceding retained
length. Removing the prefix and application leaves precisely the recorded
number of tail frames, with pointwise equality of competitor predicates. -/
theorem PiInertRunFrames.next_counted_application
    (H : PiInertRunFrames D Ω out Δ K e ck frames)
    (HE : CarrierExposure out) (hn : ¬ CarrierExposure e) :
    ∃ Θ Ξ τ pending plug depth n cs endpoint ck' K' remaining,
      PiInertRetainedPrefixCount D Δ Θ plug depth ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ (ProofShape.mkApps ((plug e).subst τ) pending) endpoint ∧
      PiInertRunFrames D Ω out Ξ K' endpoint ck' remaining ∧ ck = cs+ck' ∧
      frames = remaining+depth+1 ∧
      ∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k := by
  induction H with
  | terminal => exact (hn HE).elim
  | application HT W HTnext R HK _ =>
    exact ⟨_, _, _, _, id, 0, _, _, _, _, _, _, .refl, W, HT, HTnext, R, HK,
      rfl, by omega, fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    obtain ⟨Θ, Ξ, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, R, HR, hc, hf, EK⟩ := ih (fun H => H.not_lambda_spine _ _ _ rfl)
    exact ⟨Θ, Ξ, τ, pending, _, depth+1, n, cs, endpoint, ck', K', remaining,
      .retained SD RD WI HP, W, HTplug, HTnext, R, HR, hc, by omega,
      fun _ _ => EK _ _⟩

/-- Focus a nonempty retained prefix by reading each actual lambda path.
Exactly one frame per retained binder is rebuilt over the selected tail;
the intervening application frame is not rebuilt. The actual proof endpoint
and annotation histories derive completion transport in the inner scope.
All pending arguments are handled by lambda-spine execution, at every arity. -/
theorem PiInertRetainedPrefixCount.focus_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) (hd : 0 < depth)
    (HC : ProofEndpointContext D Θ Ξ τ)
    (HM : PiInertFrameMinimum D Ω out Ξ (ProofShape.mkApps ((plug e).subst τ) pending) cost frames) :
    ∃ Λ σ smaller, ProofEndpointContext D Δ Λ σ ∧ smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Λ (e.subst σ) smaller (frames+depth) := by
  induction H generalizing e Ξ τ pending cost frames with
  | refl => omega
  | @retained Δ A u n cd A' Θ plug depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        exact ⟨_, τ.lift, smaller, .binder RD.forget HC, hsmall, HMbody⟩
    · obtain ⟨Λ, σ, smaller, HCinner, hsmall, HMinner⟩ := ih (by omega) HC HM
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      exact ⟨_, σ.lift, last, .binder RD.forget HCinner, Nat.le_trans hlast hsmall,
        by simpa only [Nat.add_assoc] using HMbody⟩

end Lean4Lean.VEnv.Strengthening
