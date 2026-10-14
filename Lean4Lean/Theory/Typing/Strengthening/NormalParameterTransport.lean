import Lean4Lean.Theory.Typing.Strengthening.PrefixReconstructionPhase
import Lean4Lean.Theory.Typing.Strengthening.NormalHeadBetaExposure

/-! # Normal comparison across constructor parameter change

A normal comparison followed by the derived parameter-change root can be
reordered as head beta, at most one parameter change, and normal comparison.
This directional transport is stronger than merely joining the endpoints by
reversing the root on the right. Compatible and finite assembly remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Transport one constructor parameter change through normal comparison.
Only head beta computation is introduced; fields retain normal comparisons,
and the residual parameter change preserves those left fields literally. -/
theorem normal_parameter_change (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (R : ConstructorParameterChange Γ b c) :
    ∃ a0 a1, HeadBetaRed a a0 ∧ (a0 = a1 ∨ ConstructorParameterChange Γ a0 a1) ∧
      NormalEq Γ a1 c := by
  cases R with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz hb hc =>
    have ha := hb.defeqU_l henv hΓ ((H.symm hΓ).defeq hΓ)
    have hTF := constructor_unindexed_family hΓ hi hx hp hf hb
    obtain ⟨u, hT⟩ := hb.isType henv hΓ
    have hfamily := hT.defeqU_l henv hΓ hTF
    obtain ⟨n, H⟩ := H
    rcases normal_spine_expose_headBeta hΓ .const n H (bs := []) .nil ha with
      hproof | ⟨head, args, hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, hargs, hfun⟩ |
        ⟨z, A, B, m, xs, hm, RB, hzfun, HB, hargs, hfun⟩
    · exact ⟨a, a, .rfl, .inl rfl, .proofIrrel hproof ha hc⟩
    · cases hh with
      | @const exposedLevels _ _ hlevels =>
        simp only [mkApps_nil] at RB
        simp only [List.append_nil] at HA
        have ht0 := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ha).hasType.2
        have hlen : args.length = info.nparams + info.numFields := by simpa [hp, hf] using HA.length_eq
        have hpa : (args.take info.nparams).length = info.nparams := by simp [hlen]
        have hfa : (args.drop info.nparams).length = info.numFields := by simp [hlen]
        have HF : List.Forall₂ (NormalEq Γ) (args.drop info.nparams) fields := by
          have HD := List.forall₂_drop HA info.nparams
          rw [← hp, List.drop_left, hp] at HD
          exact HD
        have HP : List.Forall₂ (NormalEq Γ) params' params' :=
          NormalEqF.forall₂_refl (η := true) fun p h =>
            mkApps_arg_type hΓ hc (List.mem_append_left _ h)
        obtain ⟨C, hhead⟩ := mkApps_head_type hΓ hc
        have HF' : List.Forall₂ (NormalEq Γ) fields (args.drop info.nparams) :=
          HF.flip.imp (fun _ _ (H : NormalEq Γ _ _) => H.symm hΓ)
        have Hmid := NormalEq.mkApps_spine hΓ (.refl hhead) (HP.append' HF') hc
        have hmid := hc.defeqU_l henv hΓ (Hmid.defeq hΓ)
        have RP : ConstructorParameterChange Γ
            (mkApps (.const info.ctorName exposedLevels) args)
            (mkApps (.const info.ctorName levels') (params' ++ args.drop info.nparams)) := by
          have RP := ConstructorParameterChange.intro hi hx hpa hp' hfa hz
            (by simpa only [List.take_append_drop] using ht0) hmid
          simpa only [List.take_append_drop] using RP
        exact ⟨_, _, RB, .inr RP, Hmid.symm hΓ⟩
    · have htLam := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ha).hasType.2
      have htFam := htLam.defeqU_r henv hΓ hTF
      obtain ⟨_, hY, _⟩ := htFam.lam_inv_forallE henv hΓ
      exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily hY.symm).elim
    · have htZ := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ha).hasType.2
      have htFam := htZ.defeqU_r henv hΓ hTF
      exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily
        (htFam.uniqU henv hΓ hzfun)).elim

/-- The directional root transport embeds in the extended computational phase.
No canonical Eq, witnessed front, or parameter-phase hypothesis is required. -/
theorem normal_parameter_change_phase (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (R : ConstructorParameterChange Γ b c) :
    PrefixReconstructionJoin D Γ a c := by
  obtain ⟨a0, a1, RB, RP, HN⟩ := normal_parameter_change hΓ H R
  refine ⟨a0, c, .base (.of_beta RB.toBeta), .refl, a1, c, ?_, .refl, HN⟩
  rcases RP with rfl | RP
  · exact .refl
  · exact .parameters RP

end Lean4Lean.VEnv.Strengthening.PureObservation
