import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldRootDescent

/-! # Focus actual lambda execution while preserving the future field supply

Reading lambda bodies and nonempty retained telescopes preserves the marked
application that will supply the original type argument. Only the actual
suffix is focused; its preceding guarded computation is never substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map lambda_body_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions} {K : ProofShape → Nat → Prop}

/-- Read an actual lambda-spine minimum in its original body context while
preserving the distinguished future type-binder consumption. Either actual
lambda branch adds one frame above that binder; primitive cost cannot increase.
Competitors retain the same unrestricted all-stage/raw interpretation. -/
theorem pi_inert_lambda_spine_body_fresh_field_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource (controls ++ A :: Δ) (ProofShape.mkApps (.lam C body) args))
    (R : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam C body) args) endpoint)
    (HK : PiInertFreshFieldRun D Δ family out A x controls K endpoint ck frames)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam C body) args) tail → K tail k → ct+ck ≤ j+k) :
    ∃ smaller, smaller ≤ ct+ck ∧ PiInertFreshFieldMinimum D Δ family out A x (C :: controls)
      body smaller (frames+1) := by
  have HTlam : TypedSource (controls ++ A :: Δ) (.lam C body) := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody C .hole).typed HTlam
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨C', body', args', cf, ca, hc, rfl, RF, RX⟩ |
    ⟨C', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have hexact := HM _ _ _ ck (lambda_body_replace RD RB RX) HK.forget.forget.holds
    refine ⟨cb+ck, by omega, (fun body k => K (ProofShape.mkApps (.lam C' body) args') k),
      m, cb, ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HK
    · intro later j tail k RJ HL
      have HB := HM _ _ _ k (lambda_body_replace RD RJ RX) HL
      omega
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have WI : ContextSubstitution (C :: (controls ++ A :: Δ)) (controls ++ A :: Δ) (ProofShape.Subst.one x') := by
      intro Γ hΓ EΓ
      exact typed_lambda_argument_map heq hs HT RX hΓ EΓ
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 (controls ++ A :: Δ)
        (ProofShape.mkApps (.lam C' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := C') (b := body') (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
    have HTnext := HT.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
    have Ractual := ((lambda_body_replace RD RB RX).trans
      (Rbeta.mono (pi_inert_stage_mono (Nat.le_max_left n m)))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_left n m)))
    have hexact := HM _ _ _ ck Ractual HK.forget.forget.holds
    refine ⟨cb+(cs+ck), by omega, PiInertApplicationContinuation D (controls ++ A :: Δ) (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · exact .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WI)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    · rintro later j tail k RJ ⟨suffixStage, tailCount, last, lastCost, hsum, RT, HL⟩
      have Rprefix := lambda_body_replace RD RJ RX
      have RBeta : ScopedComputeCount (PiInertStage D (max n later)) 0 (controls ++ A :: Δ)
          (ProofShape.mkApps (.lam C' tail) (x' :: xs')) (ProofShape.mkApps (tail.inst x') xs') := by
        simpa only [ProofShape.mkApps, Nat.zero_add] using
          (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
            (BetaRed.beta (A := C') (b := tail) (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
      have RT' : ScopedComputeCount (PiInertStage D suffixStage) tailCount (controls ++ A :: Δ)
          (ProofShape.mkApps (tail.inst x') xs') last := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RT
      have RR := ((Rprefix.trans RBeta).mono
        (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
        (RT'.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
      have HB := HM _ _ _ lastCost RR HL
      omega

/-- Body readout for a marked whole-lambda minimum preserves the same future
supplying argument and adds exactly one temporary binder and frame. -/
theorem PiInertFreshFieldMinimum.lambda_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps (.lam C body) args) cost frames) :
    ∃ smaller, smaller ≤ cost ∧ PiInertFreshFieldMinimum D Δ family out A x (C :: controls)
      body smaller (frames+1) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨smaller, hsmall, Hbody⟩ := pi_inert_lambda_spine_body_fresh_field_minimum heq hs HT R HK
    (by simpa only [hc] using HM)
  exact ⟨smaller, by omega, Hbody⟩

/-- Focus a nonempty retained telescope in the actual target of an ordinary
substitution, preserving the marked future supply. The new source is the
literal interpreted endpoint under that telescope. Its original guarded path
is not transported, its remaining cost cannot increase, and precisely one
frame per retained binder is added above the selected tail. -/
theorem PiInertRetainedPrefixCount.focus_fresh_field_nonempty
    {plug : ProofShape → ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertRetainedPrefixCount D Ξ Θ plug depth) (hd : 0 < depth)
    (W : ContextSubstitution Θ (controls ++ A :: Δ) τ)
    (HM : PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps ((plug e).subst τ) pending) cost frames) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Ξ ((telescope ++ controls) ++ A :: Δ) (τ.liftN depth) ∧
      smaller ≤ cost ∧ PiInertFreshFieldMinimum D Δ family out A x (telescope ++ controls)
        (e.subst (τ.liftN depth)) smaller (frames+depth) := by
  induction H generalizing e controls τ pending cost frames with
  | refl => omega
  | @retained Ξ C v n cd C' Θ plug depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        refine ⟨[C'.subst τ], smaller, rfl, ?_, hsmall, HMbody⟩
        intro Γ hΓ EΓ
        simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
          List.cons_append, List.nil_append] using
          (ContextSubstitution.comp WI (ContextSubstitution.cons (A := C') W) hΓ EΓ)
    · obtain ⟨telescope, smaller, hlen, WS, hsmall, HMinner⟩ := ih (by omega) W HM
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      refine ⟨C'.subst (τ.liftN depth) :: telescope, last,
        by simp only [List.length_cons, hlen], ?_, Nat.le_trans hlast hsmall, ?_⟩
      · intro Γ hΓ EΓ
        simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
          List.cons_append, List.nil_append] using
          (ContextSubstitution.comp WI (ContextSubstitution.cons (A := C') WS) hΓ EΓ)
      · simpa only [Nat.add_assoc, ProofShape.Subst.liftN, List.cons_append] using HMbody

/-- Fixing the actual preceding endpoint gives a minimum at the next
application source while preserving the marked tail. The old body computation
is reused verbatim in every competing replay. -/
theorem pi_inert_fresh_field_application_minimum
    {plug : ProofShape → ProofShape}
    (RP : ScopedComputeCount (PiInertStage D n) cb Ξ source e)
    (HT : TypedSource (controls ++ A :: Δ) (ProofShape.mkApps ((plug e).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs (controls ++ A :: Δ)
      (ProofShape.mkApps ((plug e).subst τ) pending) endpoint)
    (HK : PiInertFreshFieldRun D Δ family out A x controls K' endpoint ck frames)
    (EK : ∀ body k, K body k ↔
      PiInertApplicationContinuation D (controls ++ A :: Δ) τ pending K' (plug body) k)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Ξ source body →
      K body k → cb+(cs+ck) ≤ j+k) :
    PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps ((plug e).subst τ) pending) (cs+ck) frames := by
  refine ⟨K', m, cs, ck, endpoint, HT, RT, HK, rfl, ?_⟩
  intro later j tail k RJ HL
  have HH := HM n cb e (j+k) RP ((EK _ _).2 ⟨later, j, tail, k, rfl, RJ, HL⟩)
  omega

end Lean4Lean.VEnv.Strengthening
