import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedEtaFrames

/-! # Actual body typings at an inferred lambda cut

The source frame supplies a sort assignment for its actual body. Inferred
comparison supplies a common function type, so the opposite body also has a
sort assignment in its own domain context. Reflexivity and typed eta close
frame transfer outright; the remaining cut retains an actual body-comparison
child in one of the two recorded binder contexts.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Frame typing transfers to any actual typed representative of its erasure.
This supplies a sort assignment, rather than assuming it for that original. -/
theorem RigidSortFrames.original_sort
    (H : RigidSortFrames c (proofEraseCtx Γ) (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ u, env.HasType univs Γ e (.sort u) := by
  obtain ⟨u, Γ₀, f, hΓ₀, EΓ₀, hf, Ef⟩ := H.typing
  have W := proofEraseCtx_defeq hΓ₀ hΓ EΓ₀
  have hf' := hf.defeqDFC henv W
  have Ef' := (proofErase_defeqCtx hΓ₀ W hf).symm.trans Ef
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hf' ht Ef').2 (not_isProof_of_sort hΓ hf')
  exact ⟨u, ((HE.defeq hΓ).of_l henv hΓ hf').hasType.2⟩

/-- With actual typed lambda endpoints, one framed body supplies both body
sort assignments and equality of the written domains. The target function's
original assigned type is unrestricted. Its nonproof status is recovered from
the directed lambda exposure, rather than required as a new premise. -/
theorem pi_inert_compared_lambda_body_typing
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) F) (hg : env.HasType univs Γ (.lam C d) G)
    (HB : RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d))) :
    ∃ w u, env.IsDefEq univs Γ A C (.sort w) ∧
      env.HasType univs (A :: Γ) b (.sort u) ∧ env.HasType univs (C :: Γ) d (.sort u) := by
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht HR.1
  obtain ⟨⟨w, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  obtain ⟨u, hbu⟩ := HB.original_sort hΓA hb
  have hfu := HasType.lam hA hbu
  have hnf := not_isProof_function_to_sort hΓ hfu
  have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hnf
  have HR := H
  rw [EL] at HR
  obtain ⟨_, _, _, _, _, RG, _⟩ := HR.pi_inert_lambda_cut
  have hng : ¬ IsProof Γ (.lam C d) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at RG
    cases RG.pi_inert_proof_fixed
  have HFG := (proofErase_computed_joint_compare_reflect hdsc hΓ hfu hg H).2 rfl hnf hng
  have hgu := (HFG.of_l henv hΓ hfu).hasType.2
  obtain ⟨⟨z, hC⟩, E, hd⟩ := hg.lam_inv henv hΓ
  have HPi := (HasType.lam hC hd).uniqU henv hΓ hgu
  obtain ⟨⟨_, HCA⟩, _, HE⟩ := HPi.forallE_inv henv hΓ
  have HAC := HCA.toU.symm.of_l henv hΓ hA
  exact ⟨w, u, HAC, hbu, HE.defeq hd⟩

/-- Removing terminal-rule symmetry retains the actual orientation of its
body context. Sorted-domain and ordinary-domain terminals have the same body
child; eta is kept separate from that child, as required by the raw boundary. -/
theorem InferredLambdaTerminal.body_cases (H : InferredLambdaTerminal Step Δ A b C d) :
    (A = C ∧ b = d) ∨
      ComputedJointCompare Step (A :: Δ) false b d ∨
      ComputedJointCompare Step (C :: Δ) false b d ∨
      (EtaHead (.lam A b) (.lam C d) ∨ EtaHead (.lam C d) (.lam A b)) := by
  induction H with
  | refl => exact .inl ⟨rfl, rfl⟩
  | lam _ HB | sorted _ _ _ HB => exact .inr (.inl HB)
  | eta _ HE => exact .inr (.inr (.inr HE))
  | symm _ ih =>
    rcases ih with ⟨EA, EB⟩ | HL | HR | HE
    · exact .inl ⟨EA.symm, EB.symm⟩
    · exact .inr (.inr (.inl HL.symm))
    · exact .inr (.inl HR.symm)
    · exact .inr (.inr (.inr HE.symm))

/-- Actual body typings discharge reflexivity and eta at the terminal cut.
Otherwise the result is an existing inferred body child in its recorded
annotation context, not an assumed new comparison or a transported path. -/
theorem InferredLambdaTerminal.typed_frame_or_body
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v))
    (HF : RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : InferredLambdaTerminal Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) (proofErase Γ C) (proofErase (C :: Γ) d)) :
    RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) ∨
      ComputedJointCompare Step (proofEraseCtx (A :: Γ)) false
        (proofErase (A :: Γ) b) (proofErase (C :: Γ) d) ∨
      ComputedJointCompare Step (proofEraseCtx (C :: Γ)) false
        (proofErase (A :: Γ) b) (proofErase (C :: Γ) d) := by
  rcases H.body_cases with ⟨EA, EB⟩ | HL | HR | HE
  · exact .inl (by simpa only [proofEraseCtx, EA, EB] using HF)
  · exact .inr (.inl HL)
  · exact .inr (.inr HR)
  · have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
      if_neg (not_isProof_function_to_sort hΓ (.lam HAC.hasType.1 hb))
    have ER : proofErase Γ (.lam C d) = .lam (proofErase Γ C) (proofErase (C :: Γ) d) :=
      if_neg (not_isProof_function_to_sort hΓ (.lam HAC.hasType.2 hd))
    exact .inl ((RigidSortFrames.typed_eta_pair_iff hΓ HAC hb hd (by rwa [EL, ER])).1 HF)

/-- Every inferred comparison of an actual framed-body lambda with a typed
function reaches actual lambda representatives with recovered sort-typed
bodies and equal written domains. The target body is already framed, or an
actual inferred body child remains in one of the two original cut contexts.
This neither substitutes that child at an arbitrary argument nor moves its
guarded computation across the domain equality. -/
theorem pi_inert_typed_lambda_frame_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) F) (hg : env.HasType univs Γ g G)
    (HB : RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ g)) :
    ∃ A' b' C d w u,
      env.IsDefEq univs Γ (.lam A b) (.lam A' b') F ∧
      env.IsDefEq univs Γ g (.lam C d) G ∧
      env.IsDefEq univs Γ A' C (.sort w) ∧
      env.HasType univs (A' :: Γ) b' (.sort u) ∧ env.HasType univs (C :: Γ) d (.sort u) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam A' b')) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
        (proofErase Γ g) (proofErase Γ (.lam C d)) ∧
      RigidSortFrames c (proofEraseCtx (A' :: Γ)) (proofErase (A' :: Γ) b') ∧
      (RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) ∨
        ComputedJointCompare (PiInertStage D n) (proofEraseCtx (A' :: Γ)) false
          (proofErase (A' :: Γ) b') (proofErase (C :: Γ) d) ∨
        ComputedJointCompare (PiInertStage D n) (proofEraseCtx (C :: Γ)) false
          (proofErase (A' :: Γ) b') (proofErase (C :: Γ) d)) := by
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht HR.1
  obtain ⟨⟨w₀, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨u₀, hbu⟩ := HB.original_sort ⟨hΓ, w₀, hA⟩ hb
  have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hA hbu))
  have HR := H
  rw [EL] at HR
  obtain ⟨rawA, rawb, rawC, rawd, RL, RR, HF, HT⟩ :=
    HB.inferred_lambda_cut heq hs hc hD HR
  obtain ⟨f', Hf, Ef⟩ := proofErase_scoped_compute_realize hdsc hΓ hf rfl EL RL
  obtain ⟨A', b', rfl, _, EA', Eb'⟩ := erase_lam_inv Ef
  obtain ⟨g', Hg, Eg⟩ := proofErase_scoped_compute_realize hdsc hΓ hg rfl rfl RR
  obtain ⟨C, d, rfl, _, EC, Ed⟩ := erase_lam_inv Eg
  have HF' : RigidSortFrames c (proofEraseCtx (A' :: Γ)) (proofErase (A' :: Γ) b') := by
    simpa only [proofEraseCtx, EA', Eb'] using HF
  have HT' : InferredLambdaTerminal (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ A') (proofErase (A' :: Γ) b') (proofErase Γ C) (proofErase (C :: Γ) d) := by
    simpa only [EA', Eb', EC, Ed] using HT
  have HC : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A' b')) (proofErase Γ (.lam C d)) := by
    rw [Ef, Eg]
    exact HT.compare
  obtain ⟨w, u, HAC, hbl, hdr⟩ := pi_inert_compared_lambda_body_typing heq hs hΓ
    Hf.hasType.2 Hg.hasType.2 HF' HC
  refine ⟨A', b', C, d, w, u, Hf, Hg, HAC, hbl, hdr, ?_, ?_, HF', ?_⟩
  · simpa only [EL, Ef] using RL
  · simpa only [Eg] using RR
  · exact HT'.typed_frame_or_body hΓ HAC hbl hdr HF'

end Lean4Lean.VEnv.Strengthening
