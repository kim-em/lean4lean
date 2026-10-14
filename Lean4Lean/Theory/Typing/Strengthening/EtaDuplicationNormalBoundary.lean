import Lean4Lean.Theory.Typing.Strengthening.EtaDuplicationSpineBoundary
import Lean4Lean.Theory.Typing.Strengthening.NormalHeadBetaExposure

/-! # Selective projection cannot be postponed past all eta

Head beta exposure removes the restriction that the eta endpoint be a literal
constructor spine. The two-field selective projection test has no terminal
eta/normal witness at all, under the displayed typing assumptions.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A structure eta step followed by contraction of only its first projection
cannot be represented by finite typed eta followed by normal comparison. This
is a phase-ordering obstruction, not a counterexample to strengthening. -/
theorem selective_projection_not_etaNormal
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hproj : env.HasType univs Γ (.proj family 0
      (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])) (.sort v)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    ¬ EtaNormal Γ source
      (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) := by
  intro source ⟨mid, RE, n, HN⟩
  have htMid := (RE.simAt hΓ _ ht).hasType.2
  rcases normal_spine_expose_headBeta hΓ .const n HN (bs := []) .nil htMid with
    hproof | ⟨head, args, hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, ha, hf⟩
  · exact hnp hproof
  · simp only [mkApps_nil] at RB
    cases hh with
    | const hls =>
      have RE' := eta_constant_headBeta hΓ RE ht RB
      have htOut := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction
        hΓ _ htMid).hasType.2
      obtain ⟨_, hc⟩ := mkApps_head_type hΓ htOut
      obtain ⟨ci, hci, hw, hl⟩ := hc.const_inv henv hΓ
      have htTarget := ((HN.defeq hΓ).of_l henv hΓ htMid).hasType.2
      obtain ⟨_, hc'⟩ := mkApps_head_type hΓ htTarget
      obtain ⟨_, _, hw', _⟩ := hc'.const_inv henv hΓ
      have Hhead : NormalEq Γ _ _ := .constDF hci hw hw' hl hls
      have Hwhole := NormalEq.mkApps_spine hΓ Hhead
        (by simpa only [List.append_nil] using HA) htOut
      exact selective_projection_no_constructor_middle hΓ hi hp hf hnp ht hv hproj
        _ _ ⟨RE', Hwhole⟩
  · have htLam := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction
      hΓ _ htMid).hasType.2
    obtain ⟨_, hY, _⟩ := htLam.lam_inv_forallE henv hΓ
    obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) (args := []) hfamily hY.symm
  · have htZ := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction
      hΓ _ htMid).hasType.2
    obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) (args := []) hfamily
      (htZ.uniqU henv hΓ hz)

end Lean4Lean.VEnv.Strengthening.PureObservation
