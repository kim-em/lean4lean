import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIdentityCarrierExposure

/-! # Inferred computed comparisons through shared typed templates

The new exposed endpoints already compare in inferred mode. Such comparisons
can be substituted into a shared typed template without resynthesis or a
computation join. This supports checking dependent field-type recipes while
keeping distinct endpoint histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Inferred comparisons of images extend through every shared typed template.
Only the left image map needs a typed interpretation to supply binder scopes.
The result stays in the original computed checker and at the same stage;
no native-carrier resynthesis or joining of image computations is assumed. -/
theorem proofErase_computed_joint_subst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (he : env.HasType univs Γ e T) (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (H : ∀ i, ComputedJointCompare Step (proofEraseCtx Γ₀) false (ρ i) (τ i)) :
    ComputedJointCompare Step (proofEraseCtx Γ₀) false
      ((proofErase Γ e).subst ρ) ((proofErase Γ e).subst τ) := by
  classical
  induction e generalizing Γ Γ₀ σ ρ τ T with
  | bvar i =>
    by_cases hp : IsProof Γ (.bvar i)
    · rw [proofErase_eq_proof.2 hp]; exact .leaf .refl
    simpa only [proofErase, if_neg hp, ProofShape.subst] using H i
  | sort u => simp only [proofErase]; split <;> exact .leaf .refl
  | const c ls => simp only [proofErase]; split <;> exact .leaf .refl
  | app f a ihf iha =>
    by_cases hp : IsProof Γ (.app f a)
    · rw [proofErase_eq_proof.2 hp]; exact .leaf .refl
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .app (ihf hΓ₀ W hf E H) (iha hΓ₀ W ha E H).common
  | proj s i m ih =>
    by_cases hp : IsProof Γ (.proj s i m)
    · rw [proofErase_eq_proof.2 hp]; exact .leaf .refl
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .proj (ih hΓ₀ W hm.hasType.2 E H)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [proofErase]
    split
    · exact .leaf .refl
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact he.lam_inv henv W.wf | exact he.forallE_inv henv
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    have HH : ∀ i, ComputedJointCompare Step (proofEraseCtx (A.subst σ :: Γ₀)) false
        (ρ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .leaf .refl
      | succ i =>
        have HR := (H i).rename hrename (ContextRenaming.of_liftN hΓ₀ hΓA' Ctx.LiftN.one)
        simpa only [JointCheckKind.subst, subst_bvar_liftN, ProofShape.Subst.lift] using HR
    have HB := ihb hΓA' (W.lift henv.ordered hA) hb (E.lift hΓ₀ W hA) HH
    rw [show proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ from
      congrArg (· :: proofEraseCtx Γ₀) (proofErase_subst_with hΓ₀ W hA E)] at HB
    simp only [ProofShape.subst]
    first | exact .lam (ihA hΓ₀ W hA E H) HB | exact .forallE (ihA hΓ₀ W hA E H) HB

/-- Two differently supplied but inferred-compared arguments instantiate a
shared typed body in inferred mode. Both actual substitutions are retained. -/
theorem proofErase_computed_joint_inst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HC := proofErase_computed_joint_subst_images hrename hΓA.1 W hb
    (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one (proofErase Γ y)) (fun i => by
      cases i with
      | zero => exact H
      | succ i => exact .leaf .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hy Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HC

/-- Inferred comparison of a closed telescope's capture vector propagates
through its entire typed body, including dependent type recipes. Only the
left vector needs telescope typing; the right vector can be raw images. -/
theorem proofErase_computed_template_compare_captures
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (he : env.HasType univs doms.reverse e T) (ha : TelInst env univs Γ doms args)
    (H : List.Forall₂ (ComputedJointCompare Step (proofEraseCtx Γ) false)
      (args.map (proofErase Γ)) rawArgs) :
    ComputedJointCompare Step (proofEraseCtx Γ) false
      ((proofErase doms.reverse e).instOuter (args.map (proofErase Γ)))
      ((proofErase doms.reverse e).instOuter rawArgs) := by
  have W := erasedTemplate_substEq hΔ ha
  have E : ErasedSubstAgreement doms.reverse Γ (VExpr.Subst.ofList args)
      (ProofShape.Subst.ofList (args.map (proofErase Γ))) := by
    intro i A hl _
    have hi : i < args.length := by
      have := hl.lt
      have := ha.1
      simp only [List.length_reverse] at *
      omega
    simp only [VExpr.Subst.ofList, ProofShape.Subst.ofList, List.length_map, dif_pos hi,
      List.getElem_map]
  apply proofErase_computed_joint_subst_images hrename hΓ W he E
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < (args.map (proofErase Γ)).length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .leaf .refl

/-- Exposed identity-wrapped endpoints give stage-zero inferred comparison of
all instances of a shared typed body. Their computations need not join and
may have changed the selected carrier to a new native annotation. -/
theorem identity_carrier_exposure_template_outputs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (ht : env.HasType univs (A :: Γ) t T)
    (hnx : ¬ IsProof Γ x) (hny : ¬ IsProof Γ y)
    (H : IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ∃ C x' y', ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ A) C ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) x)) (proofErase Γ x') ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) y)) (proofErase Γ y') ∧
      env.HasType univs Γ x' A ∧ env.HasType univs Γ y' A ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ x') C ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ y') C ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
        (proofErase Γ (t.inst x')) (proofErase Γ (t.inst y')) := by
  obtain ⟨C, a, b, RC, RX, RY, NX, NY, HG⟩ := H.native_compared_outputs (mode := false)
  rw [← proofErase_nativeIdentityExpansion hΓ hx hnx] at RX
  rw [← proofErase_nativeIdentityExpansion hΓ hy hny] at RY
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ
    (nativeIdentityExpansion_equal hx).hasType.1 rfl rfl RX
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ
    (nativeIdentityExpansion_equal hy).hasType.1 rfl rfl RY
  rw [← EX] at RX NX HG
  rw [← EY] at RY NY HG
  exact ⟨C, x', y', RC, RX, RY, HX.hasType.2, HY.hasType.2, NX, NY,
    proofErase_computed_joint_inst_images (erased_static_structure_eta_expansion_stage_rename heq hs 0)
      ⟨hΓ, u, hA⟩ ht HX.hasType.2 HY.hasType.2 HG⟩

end Lean4Lean.VEnv.Strengthening
