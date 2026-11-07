import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSpineTypeExposure

/-! # Three origins of a computed selectable projection

A minimum-count projection path retains its projection, has already selected
the original field, or retains a whole constant control wrapper. Consumed
wrappers can be bypassed with strictly fewer primitive occurrences.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every stage-zero continuation of a typed immediately selectable projection
has one of three origins: a retained projection with its major path, a direct
path from the selected field, or a whole constant wrapper with a universe-typed
control argument. The wrapper payload retains a path from the original
projection; no comparison-closure premise is supplied. -/
theorem pi_inert_zero_selected_projection_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ (.proj family i m))
    (RI : Primitive D (.proj family i m) field)
    (R : ScopedCompute (PiInertStage D 0) Δ (.proj family i m) out) :
    (∃ major, out = .proj family i major ∧ ScopedCompute (PiInertStage D 0) Δ m major) ∨
    ScopedCompute (PiInertStage D 0) Δ field out ∨
    (∃ A payload x, out = .app (.lam A (payload.liftN 1)) x ∧
      ScopedCompute (PiInertStage D 0) Δ (.proj family i m) payload ∧
      ControlTyping Δ x (.sort (.succ .zero))) := by
  obtain ⟨cost, RC, hmin⟩ := R.minimal_count
  rcases RC.projection_first_root with ⟨major, EO, RM⟩ |
      ⟨major, target, before, after, HC, RM, HR, RT⟩
  · exact .inl ⟨major, EO, RM.forget⟩
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  rcases HR.1 with HR | HE
  · obtain ⟨info', levels, args, hi', EM, hl, hg⟩ := erased_level_core_projection_root HR
    have RI' : Primitive D (.proj family i major) target := by
      rw [EM]; exact .projIota hi' hl hg
    have hout : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
      rw [EM]
      intro A b rest E
      have EC := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at EC
      cases EC
    obtain ⟨selected, RI'', RF⟩ := pi_inert_zero_constructor_selection_residual
      heq hs hi hD ((ScopedHole.proj family i .hole).typed HT) RI hout RM.forget
    have E := RI''.projection_deterministic RI'
    exact .inr (.inl (RF.trans (E ▸ RT.forget)))
  cases HE with
  | intro _ =>
    have HTP := HT.pi_inert_compute heq hs (ScopedCompute.proj RM.forget)
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTP
    have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
      .sort (by trivial)
    have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
      if_neg (not_isProof_of_sort hΓ hA)
    change ScopedComputeCount (PiInertStage D 0) after Δ
      (ProofShape.mkApps (.lam (.sort (.succ .zero)) ((ProofShape.proj family i major).liftN 1))
        [.sort .zero]) out at RT
    rcases RT.pi_inert_lambda_spine_or_beta with
      ⟨rawA, rawb, args', cf, ca, hc, EO, RF, RX⟩ |
      ⟨rawA, rawb, x', xs', cf, ca, tail, hc, RF, RX, Rtail⟩
    · obtain ⟨A', e', cb, hcb, _, _, EF, RE⟩ :=
        pi_inert_constant_lambda_count_readout heq hs hΓ hA ht EΓ
          (by simpa only [EA, Ee] using RF)
      cases RX with
      | cons RX0 RXnil =>
        cases RXnil
        rw [EF] at EO
        have RE' : ScopedCompute (PiInertStage D 0) Δ
            (.proj family i major) (proofErase Γ e') := by
          simpa only [EΓ, Ee] using RE.forget
        have HS : ControlTyping Δ (.sort .zero) (.sort (.succ .zero)) := by
          have htS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
          exact ⟨Γ, _, hΓ, EΓ, htS, if_neg (not_isProof_of_sort hΓ htS)⟩
        exact .inr (.inr ⟨_, _, _, EO, (ScopedCompute.proj RM.forget).trans RE', HS.compute @hd RX0.forget⟩)
    · obtain ⟨A', e', cb, hcb, _, _, EF, RE⟩ :=
        pi_inert_constant_lambda_count_readout heq hs hΓ hA ht EΓ
          (by simpa only [EA, Ee] using RF)
      cases EF
      cases RX with
      | cons _ RXnil =>
        cases RXnil
        have RE' : ScopedComputeCount (PiInertStage D 0) cb Δ
            (.proj family i major) (proofErase Γ e') := by
          simpa only [EΓ, Ee] using RE
        have Rtail' : ScopedComputeCount (PiInertStage D 0) tail Δ (proofErase Γ e') out := by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
            ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.mkApps] using Rtail
        have HM := hmin _ ((ScopedComputeCount.proj RM).trans (RE'.trans Rtail'))
        omega

end Lean4Lean.VEnv.Strengthening
