import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTerminalReadoutInduction

/-! # Focus an actual execution while reconstructing all raw competitors

Unlike a minimum-only focus, this records a fixed overhead and reconstructs
every raw body competitor in the original outer continuation. It supplies the
missing composition invariant for nested retained-prefix ancestry readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- An actual body execution at a bounded total cost, with a fixed overhead
for reconstructing EVERY raw body competitor in the original continuation.
The image and rebuild functions are syntax maps; competitors need no typing.
The selected body run retains its exact frame count. -/
def PiInertProjectionExecutionFocus (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape)
    (Ξ : List ProofShape) (K : ProofShape → Nat → Prop) (cost : Nat)
    (Λ : List ProofShape) (body : ProofShape) (frames : Nat)
    (image rebuild : ProofShape → ProofShape) : Prop :=
  ∃ stage cb endpoint kb KB overhead,
    TypedSource Λ body ∧ ScopedComputeCount (PiInertStage D stage) cb Λ body endpoint ∧
    PiInertProjectionRunFrames D Ω family index out Λ KB endpoint kb frames ∧
    overhead+cb+kb ≤ cost ∧
    ∀ candidate later j major k,
      ScopedComputeCount (PiInertStage D later) j Λ (image candidate) major → KB major k →
      PiInertApplicationContinuation D Ξ ProofShape.Subst.id [] K (rebuild candidate) (overhead+j+k)

/-- Peel an actual lambda-spine computation into its body execution, keeping
one frame over the actual suffix. Both survival and consumption preserve a
uniform raw-competitor reconstruction at a fixed domain/argument overhead.
The body computation is arbitrary and no global minimum is required. -/
theorem pi_inert_lambda_execution_focus
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A body) args) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K endpoint ck frames) :
    PiInertProjectionExecutionFocus D Ω family index out Δ K (ct+ck)
      (A :: Δ) body (frames+1) id (fun candidate => ProofShape.mkApps (.lam A candidate) args) := by
  have HTlam := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody A .hole).typed HTlam
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨C, body', args', cf, ca, hc, rfl, RL, RX⟩ |
    ⟨C, body', x, xs, cf, ca, cs, hc, RL, RX, RS⟩
  · obtain ⟨v, cd, cb, bodyStage, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RL
    refine ⟨bodyStage, cb, body', ck, (fun b k => K (ProofShape.mkApps (.lam C b) args') k),
      cd+ca, HTbody, RB, ?_, by omega, ?_⟩
    · exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HK
    · intro candidate later j major k RJ RK
      have RWrap := (ScopedComputeCount.lam
        (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
        (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
      refine ⟨max n later, cd+j+ca, ProofShape.mkApps (.lam C major) args', k, by omega, ?_, RK⟩
      simpa only [ProofShape.subst_id, ProofShape.mkApps, id_eq] using RWrap
  · obtain ⟨v, cd, cb, bodyStage, _, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RL
    have WX : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) :=
      typed_lambda_argument_map heq hs HT RX
    have RBeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam C body') (x :: xs)) (ProofShape.mkApps (body'.inst x) xs) := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := C) (b := body') (a := x))).mkApps (ScopedArgumentsCount.refl (args := xs))
    have HTnext := HT.pi_inert_compute heq hs ((RL.mkApps RX).trans RBeta).forget
    refine ⟨bodyStage, cb, body', cs+ck,
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) xs K, cd+ca,
      HTbody, RB, ?_, by omega, ?_⟩
    · exact .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WX)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    · rintro candidate later j major k RJ ⟨suffixStage, a, last, b, hsum, RA, HB⟩
      have RWrap := (ScopedComputeCount.lam
        (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
        (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
      have RConsume : ScopedComputeCount (PiInertStage D (max n later)) 0 Δ
          (ProofShape.mkApps (.lam C major) (x :: xs))
          (ProofShape.mkApps (major.subst (ProofShape.Subst.one x)) xs) := by
        simpa only [ProofShape.mkApps, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Nat.zero_add] using
          (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
            (BetaRed.beta (A := C) (b := major) (a := x))).mkApps (ScopedArgumentsCount.refl (args := xs))
      have RAlt := ((RWrap.trans RConsume).mono
        (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
        (RA.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
      refine ⟨max (max n later) suffixStage, cd+j+ca+a, last, b, by omega, ?_, HB⟩
      simpa only [ProofShape.subst_id, ProofShape.mkApps, id_eq, Nat.add_zero] using RAlt

/-- Focus any nonempty retained prefix in the target of its actual outer
context map. The exact lifted map and binder depth are preserved. Every raw
competitor at the final inner body reconstructs the ORIGINAL outer application
predicate with one fixed overhead. The body run has precisely depth extra
frames, so the original application frame is removed. -/
theorem PiInertRetainedPrefixCount.focus_execution_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HP : PiInertRetainedPrefixCount D Δ Θ plug depth) (hd : 0 < depth)
    (W : ContextSubstitution Θ Ξ τ)
    (HT : TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Ξ K endpoint ck frames) :
    ∃ telescope, telescope.length = depth ∧
      ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧
      PiInertProjectionExecutionFocus D Ω family index out Ξ K (ct+ck)
        (telescope ++ Ξ) (e.subst (τ.liftN depth)) (frames+depth)
        (fun candidate => candidate.subst (τ.liftN depth))
        (fun candidate => ProofShape.mkApps ((plug candidate).subst τ) pending) := by
  induction HP generalizing e Ξ τ pending n ct endpoint ck frames K with
  | refl => omega
  | @retained Δ A u domainStage oldDomainCost A' Θ plug depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HT RT
        obtain ⟨stage, cb, bodyEnd, kb, KB, overhead, HTbody, RB, HB, hc, rebuild⟩ :=
          pi_inert_lambda_execution_focus heq hs HT RT HK
        refine ⟨[A'.subst τ], rfl, ?_, stage, cb, bodyEnd, kb, KB, overhead,
          HTbody, RB, HB, hc, ?_⟩
        · intro Γ hΓ EΓ
          simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
            List.cons_append, List.nil_append] using
            ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') W) hΓ EΓ
        · intro candidate later j major k RJ RK
          have HR := rebuild (candidate.subst τ.lift) later j major k RJ RK
          simpa only [id_eq, ProofShape.Subst.liftN, ProofShape.subst_mkApps,
            ProofShape.subst, ProofShape.mkApps_append] using HR
    · obtain ⟨telescope, hlen, WS, stage, cb, bodyEnd, kb, KB, overhead,
        HTinner, RInner, HInner, hcost, rebuild⟩ := ih (by omega) W HT RT HK
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HTinner RInner
      obtain ⟨lastStage, lastBodyCost, lastBody, lastTailCost, KL, extra,
        HTbody, RB, HB, hlast, rebuildInner⟩ :=
        pi_inert_lambda_execution_focus heq hs HTinner RInner HInner
      refine ⟨A'.subst (τ.liftN depth) :: telescope, by simp only [List.length_cons, hlen], ?_,
        lastStage, lastBodyCost, lastBody, lastTailCost, KL, overhead+extra,
        HTbody, RB, ?_, by omega, ?_⟩
      · intro Γ hΓ EΓ
        simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
          List.cons_append, List.nil_append] using
          ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') WS) hΓ EΓ
      · simpa only [Nat.add_assoc, ProofShape.Subst.liftN, List.cons_append] using HB
      · intro candidate later j major k RJ RK
        obtain ⟨middleStage, a, middle, b, hab, RA, HA⟩ :=
          rebuildInner (candidate.subst (τ.liftN depth).lift) later j major k RJ RK
        have RA' : ScopedComputeCount (PiInertStage D middleStage) a (telescope ++ Ξ)
            ((ProofShape.mkApps (.lam A' candidate) args).subst (τ.liftN depth)) middle := by
          simpa only [ProofShape.subst_id, ProofShape.mkApps, ProofShape.subst_mkApps, ProofShape.subst] using RA
        have HR := rebuild (ProofShape.mkApps (.lam A' candidate) args) middleStage a middle b RA' HA
        have htotal : overhead+a+b = overhead+extra+j+k := by omega
        exact htotal ▸ HR

end Lean4Lean.VEnv.Strengthening
