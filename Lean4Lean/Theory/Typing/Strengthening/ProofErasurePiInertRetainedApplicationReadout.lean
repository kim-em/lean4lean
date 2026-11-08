import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertApplicationReadoutInduction

/-! # Read ancestry through a retained lambda and its next application

The actual lambda-body computation is unrestricted. Both surviving and
consumed lambda branches give a body execution with one fewer total frame,
at no larger primitive cost. Apply ancestry readout there, then rebuild the
actual domain and argument computations around the raw body competitor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- A retained pair lambda followed by an actual application admits ancestry
readout from body executions with ONE FEWER total frame, at no larger cost.
The mapped lambda may survive or be consumed; its body computation may select
arbitrary native roots. No component-only body certificate is required.

The ordinary annotation interpretation is the one supplied by the original
retained frame. It is composed with the lifted actual outer endpoint map.
Only ordinary projected terminal selection crosses that map; the original
major path and all reconstructed guarded paths retain their own scopes. -/
theorem pi_inert_retained_application_ancestry_readout
    {field value : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (WI : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id)
    (W : PiInertEndpointMap Δ Θ τ)
    (HFull : TypedSource Θ (ProofShape.mkApps
      (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift]))
      (args.map (·.subst τ) ++ pending)))
    (RT : ScopedComputeCount (PiInertStage D n) ct Θ (ProofShape.mkApps
      (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift]))
      (args.map (·.subst τ) ++ pending)) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Θ K endpoint ck frames)
    (IH : ∀ bodyCost, bodyCost ≤ ct+ck →
      PiInertPairAncestryReadoutFrames D Ω family info out bodyCost (frames+1))
    (HSort : ControlTyping (A :: Δ) (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost (A :: Δ)
      (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ct+ck ∧
      ScopedComputeCount (PiInertStage D later) j (A :: Δ) source major ∧
      PiInertApplicationContinuation D Θ τ pending K (ProofShape.mkApps (.lam A' major) args) k := by
  have WBody : ContextSubstitution (A :: Δ) (A'.subst τ :: Θ) τ.lift := by
    intro Γ hΓ EΓ
    simpa only [ProofShape.Subst.comp, ProofShape.Subst.id, ProofShape.subst] using
      ContextSubstitution.comp WI (ContextSubstitution.cons W.interpretation) hΓ EΓ
  have HTlam := typed_spine_head HFull
  have HTbody := (ScopedHole.lamBody (A'.subst τ) .hole).typed HTlam
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨C, body', args', cf, ca, hc, rfl, RL, RX⟩ |
    ⟨C, body', x, xs, cf, ca, cs, hc, RL, RX, RS⟩
  · obtain ⟨v, cd, cb, bodyStage, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RL
    have HBody : PiInertProjectionRunFrames D Ω family 0 out (A'.subst τ :: Θ)
        (fun body k => K (ProofShape.mkApps (.lam C body) args') k) body' ck (frames+1) :=
      .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HK
    obtain ⟨before, cm, later, j, major, k, hcost, RM, RJ, RK⟩ :=
      pi_inert_substitution_ancestry_readout heq hs WBody HTbody RB HBody
        (IH (cb+ck) (by omega)) HSort HD RF
    have RWrap := (ScopedComputeCount.lam
      (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
      (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
    refine ⟨fieldStage, cm, before, cd+j+ca+k, by omega, RM,
      max n later, cd+j+ca, ProofShape.mkApps (.lam C major) args', k, rfl, ?_, RK⟩
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RWrap
  · obtain ⟨v, cd, cb, bodyStage, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RL
    have WX : ContextSubstitution (A'.subst τ :: Θ) Θ (ProofShape.Subst.one x) :=
      typed_lambda_argument_map heq hs HFull RX
    have RBeta : ScopedComputeCount (PiInertStage D n) 0 Θ
        (ProofShape.mkApps (.lam C body') (x :: xs)) (ProofShape.mkApps (body'.inst x) xs) := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := C) (b := body') (a := x))).mkApps (ScopedArgumentsCount.refl (args := xs))
    have HTnext := HFull.pi_inert_compute heq hs ((RL.mkApps RX).trans RBeta).forget
    have HBody : PiInertProjectionRunFrames D Ω family 0 out (A'.subst τ :: Θ)
        (PiInertApplicationContinuation D Θ (ProofShape.Subst.one x) xs K) body' (cs+ck) (frames+1) :=
      .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WX)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    obtain ⟨before, cm, later, j, major, k, hcost, RM, RJ, RK⟩ :=
      pi_inert_substitution_ancestry_readout heq hs WBody HTbody RB HBody
        (IH (cb+(cs+ck)) (by omega)) HSort HD RF
    obtain ⟨suffixStage, a, last, b, hsum, RA, HB⟩ := RK
    have RWrap := (ScopedComputeCount.lam
      (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
      (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
    have RConsume : ScopedComputeCount (PiInertStage D (max n later)) 0 Θ
        (ProofShape.mkApps (.lam C major) (x :: xs))
        (ProofShape.mkApps (major.subst (ProofShape.Subst.one x)) xs) := by
      simpa only [ProofShape.mkApps, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
          (BetaRed.beta (A := C) (b := major) (a := x))).mkApps (ScopedArgumentsCount.refl (args := xs))
    have RAlt := ((RWrap.trans RConsume).mono
      (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
      (RA.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
    refine ⟨fieldStage, cm, before, cd+j+ca+a+b, by omega, RM,
      max (max n later) suffixStage, cd+j+ca+a, last, b, rfl, ?_, HB⟩
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append, Nat.add_zero] using RAlt

/-- The same retained/application progress includes an actual component
prefix in the original body context. First-field computation is charged to
its incoming ancestry before any annotation or endpoint map is interpreted.
The recursive body run still has one fewer total frame, and its cost is at
most the suffix cost, hence at most the full prefix-plus-suffix budget. -/
theorem pi_inert_components_retained_application_ancestry_readout
    {nextField nextValue : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RA : ScopedArgumentsCount (PiInertStage D componentStage) (A :: Δ) ca
      [field, value] [nextField, nextValue])
    (WI : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id)
    (W : PiInertEndpointMap Δ Θ τ)
    (HFull : TypedSource Θ (ProofShape.mkApps
      (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [nextField.subst τ.lift, nextValue.subst τ.lift]))
      (args.map (·.subst τ) ++ pending)))
    (RT : ScopedComputeCount (PiInertStage D n) ct Θ (ProofShape.mkApps
      (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [nextField.subst τ.lift, nextValue.subst τ.lift]))
      (args.map (·.subst τ) ++ pending)) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Θ K endpoint ck frames)
    (IH : ∀ bodyCost, bodyCost ≤ ct+ck →
      PiInertPairAncestryReadoutFrames D Ω family info out bodyCost (frames+1))
    (HSort : ControlTyping (A :: Δ) (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost (A :: Δ)
      (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ca+ct+ck ∧
      ScopedComputeCount (PiInertStage D later) j (A :: Δ) source major ∧
      PiInertApplicationContinuation D Θ τ pending K (ProofShape.mkApps (.lam A' major) args) k := by
  have HTfield : TypedSource (A :: Δ) field :=
    (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) value).typed HT
  cases RA with
  | cons RField rest =>
    cases rest with
    | cons RValue last =>
      cases last
      obtain ⟨nextLower, cNext, hcNext, RNext, HDNext⟩ := HD.compute heq hs HTfield RField
      have RAncestry := (RF.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage componentStage))).trans
        (RNext.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage componentStage)))
      obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := pi_inert_retained_application_ancestry_readout
        heq hs WI W HFull RT HK IH HSort HDNext RAncestry
      exact ⟨later, j, major, k, by omega, RJ, RK⟩

end Lean4Lean.VEnv.Strengthening
