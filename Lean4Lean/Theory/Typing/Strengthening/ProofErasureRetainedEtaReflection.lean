import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedNeutralEtaChecking

/-! # Eta reflection retaining domain history and argument classification

The raw common-mode result forgets which eta argument was selected and where
its annotation came from. Retaining both permits inferred readout after a
native domain has been supplied, including when computation crosses beta and
exposes a lambda. Functions and finite core paths are unrestricted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Reflected eta bodies retain the original argument's sort classification.
The lambda case records an exact common body, independently of its annotation. -/
def ClassifiedEtaBody (u : VLevel) (body f : ProofShape) : Prop :=
  body = .app (f.liftN 1) (etaArgument u) ∨ ∃ C, f = .lam C body
end ProofShape

variable [Params] {D : Definitions}

/-- Following the short function preserves the outer annotation literally and
the original fresh-argument classification. No normalization is required. -/
theorem ProofShape.ClassifiedEtaBody.level_compute_right
    (H : ClassifiedEtaBody u body f) (R : Compute (ErasedLevelCore D) f g) :
    ∃ body', Compute (ErasedLevelCore D) body body' ∧ ClassifiedEtaBody u body' g := by
  rcases H with rfl | ⟨C, rfl⟩
  · refine ⟨_, .app (R.liftN ?_) .refl, .inl rfl⟩
    intro a b n k H
    rcases H with H | H
    · exact .inl (erased_iota_primitive_liftN H)
    · cases H with
      | sort H hw => exact .inr (.sort H hw)
      | const H hw => exact .inr (.const H hw)
  · obtain ⟨C', body', rfl, _, RB⟩ := R.level_core_lam_inv
    exact ⟨body', RB, .inr ⟨C', rfl⟩⟩

/-- Ordinary fresh-application reflection keeps the selected eta argument in
both proof modes, rather than replacing it by an unclassified eta head. -/
theorem proofErase_ordinary_fresh_application_classified
    (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : Compute (ErasedIotaPrimitive D)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) body) :
    ∃ f', Compute (ErasedIotaPrimitive D) (proofErase Γ f) f' ∧
      ClassifiedEtaBody u body f' := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨out, R0, EO⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓA hopen (E.symm ▸ R)
  obtain ⟨g, RF, H⟩ := R0.fresh_application
  have HF := RF.simAt hs hΓ _ hf
  have hg := HF.hasType.2
  have hng := mt (isProof_congr hΓ HF).2 hn
  refine ⟨proofErase Γ g, proofErase_pattern_compute_forward hs hcon hΓ hf RF, ?_⟩
  rcases H with rfl | ⟨C, rfl⟩
  · exact .inl (EO.symm.trans (proofErase_eta_body hΓ hA hg hng))
  · obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
    obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
    have EB := proofErase_defeqCtx (Γ₁ := C :: Γ) ⟨hΓ, _, hC⟩ (.succ .zero HCA) hb
    refine .inr ⟨proofErase Γ C, ?_⟩
    rw [show proofErase Γ (.lam C out) =
      .lam (proofErase Γ C) (proofErase (C :: Γ) out) from if_neg hng, EB, EO]

/-- Independent full-core paths from an arbitrary typed eta pair have reflected
residuals retaining the domain path, an actual short representative at the
original Pi, and the exact argument classification. This does not require a
history to a neutral, a native recovery premise, or termination. -/
theorem proofErase_level_core_eta_retained_residual
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (RL : Compute (ErasedLevelCore D)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) left)
    (RF : Compute (ErasedLevelCore D) (proofErase Γ f) right) :
    ∃ X body g,
      Compute (ErasedLevelCore D) left (.lam X body) ∧
      Compute (ErasedLevelCore D) right (proofErase Γ g) ∧
      Compute (ErasedLevelCore D) (proofErase Γ A) X ∧
      env.HasType univs Γ g (.forallE A B) ∧ ¬ IsProof Γ g ∧
      ClassifiedEtaBody u body (proofErase Γ g) := by
  obtain ⟨X, body, rfl, RA, RB⟩ := RL.level_core_lam_inv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓA hopen (E.symm ▸ RB)
  obtain ⟨f', RR, Hη⟩ := proofErase_ordinary_fresh_application_classified hs hcon hΓ hA hf hn (E ▸ RM)
  obtain ⟨common, RF', RR'⟩ := hc hΓ hf RF (RR.mono (fun H => .inl H))
  obtain ⟨body', RB', Hη'⟩ := Hη.level_compute_right RR'
  obtain ⟨g, HG, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hf rfl rfl ((RF.trans RF').scoped (fun H => .base H))
  exact ⟨X, body', g, .lam .refl (RT.trans RB'), EG ▸ RF', RA,
    HG.hasType.2, mt (isProof_congr hΓ HG).2 hn, EG ▸ Hη'⟩

/-- A classified residual of an actual function admits inferred readout when
its retained outer domain compares with one selected native domain. In the
lambda case typed proof erasure validates beta at the original argument sort;
no literal equality or core join of the two written annotations is assumed. -/
theorem classified_eta_native_domain_check
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ClassifiedEtaBody u body (proofErase Γ f))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE C E))
    (SC : DomainSort (proofEraseCtx Γ) C u)
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) false X C) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode (.lam X body) (proofErase Γ f) := by
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) (proofErase Γ f)
      (.lam C (.app ((proofErase Γ f).liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN SC))))))
  rcases H with rfl | ⟨Y, EY⟩
  · exact .compute .refl RE (.lam HX (.leaf .refl))
  · obtain ⟨A', b, rfl, _, EA, EB⟩ := erase_lam_inv EY
    obtain ⟨⟨v, hA'⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, HAA⟩, _⟩ := ((HasType.lam hA' hb).uniqU henv hΓ hf).forallE_inv henv hΓ
    have hAu := hA.defeqU_l henv hΓ HAA.toU.symm
    have RB : ProofShape.BetaRed
        (.lam C (.app ((proofErase Γ (.lam A' b)).liftN 1) (etaArgument u))) (.lam C body) := by
      simpa only [EY, EA, EB] using proofErase_eta_lambda_beta hΓ hAu hb C
    exact .compute .refl (RE.trans (.beta RB)) (.lam HX (.leaf .refl))

/-- Inferred eta residual comparison for unrestricted functions reduces to
retained native-domain coverage along their core descendants. The missing
coverage is explicit: recover a Pi at each descendant and compare its selected
domain with each computed written annotation, at one supplied finite stage.
This theorem does not establish that coverage or arbitrary consumer closure. -/
theorem proofErase_level_core_eta_check_of_native_domains
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (Hnative : ∀ {g X}, Compute (ErasedLevelCore D) (proofErase Γ f) (proofErase Γ g) →
      env.HasType univs Γ g (.forallE A B) →
      Compute (ErasedLevelCore D) (proofErase Γ A) X →
      ∃ C E, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ) (proofErase Γ g) (.forallE C E) ∧ DomainSort (proofEraseCtx Γ) C u ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
          (proofEraseCtx Γ) false X C)
    (RL : Compute (ErasedLevelCore D)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) left)
    (RF : Compute (ErasedLevelCore D) (proofErase Γ f) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  obtain ⟨X, body, g, RL', RF', RA, hg, _, Hη⟩ :=
    proofErase_level_core_eta_retained_residual hs hl hcon hc hΓ hA hf hn RL RF
  obtain ⟨C, E, RN, SC, HX⟩ := Hnative (RF.trans RF') hg RA
  exact .compute RL'.in_static_stage RF'.in_static_stage
    (classified_eta_native_domain_check hΓ hA hg Hη RN SC HX)

/-- Each finite residual pair may choose its own finite stage; no uniform bound
on all descendants is needed. Proof-valued functions are handled by core
confluence. Native-domain coverage for non-proof descendants remains the exact
missing premise, and no completeness of that coverage is asserted. -/
theorem proofErase_level_core_eta_finite_check_of_native_domains
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (Hnative : ∀ {g X}, Compute (ErasedLevelCore D) (proofErase Γ f) (proofErase Γ g) →
      env.HasType univs Γ g (.forallE A B) → ¬ IsProof Γ g →
      Compute (ErasedLevelCore D) (proofErase Γ A) X →
      ∃ stage C E, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ) (proofErase Γ g) (.forallE C E) ∧ DomainSort (proofEraseCtx Γ) C u ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
          (proofEraseCtx Γ) false X C)
    (RL : Compute (ErasedLevelCore D)
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) left)
    (RF : Compute (ErasedLevelCore D) (proofErase Γ f) right) :
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) mode left right := by
  by_cases hn : IsProof Γ f
  · have EE : proofErase Γ (.lam A (.app f.lift (.bvar 0))) = proofErase Γ f := by
      rw [proofErase_eq_proof.2 hn,
        proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hn)]
    rw [EE] at RL
    obtain ⟨shared, RL', RF'⟩ := hc hΓ hf RL RF
    exact ⟨0, .compute RL'.in_static_stage RF'.in_static_stage (.leaf .refl)⟩
  · rw [proofErase_nativeEtaExpansion hΓ hA hf hn] at RL
    obtain ⟨X, body, g, RL', RF', RA, hg, hng, Hη⟩ :=
      proofErase_level_core_eta_retained_residual hs hl hcon hc hΓ hA hf hn RL RF
    obtain ⟨stage, C, E, RN, SC, HX⟩ := Hnative (RF.trans RF') hg hng RA
    exact ⟨stage+1, .compute RL'.in_static_stage RF'.in_static_stage
      (classified_eta_native_domain_check hΓ hA hg Hη RN SC HX)⟩

end Lean4Lean.VEnv.Strengthening
