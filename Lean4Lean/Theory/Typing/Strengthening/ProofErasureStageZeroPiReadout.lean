import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredPiTrace

/-! # Stage-zero Pi readout without an increase in stage

The general union readout transports codomain histories through computed
binders. At stage zero the primitive relation is context independent, so
those histories can instead be recontextualized directly. This preserves the
original stage through arbitrary constant expansions and beta interleavings.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
variable [Params] {D : PureObservation.Definitions}

/-- A payload records actual component representatives and computation from
the initial Pi. Its codomain history stays in the initial binder context. -/
def StageZeroPiOrigin (D : PureObservation.Definitions) (Γ : List VExpr)
    (A B : VExpr) (u v : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A' B', env.IsDefEq univs Γ A A' (.sort u) ∧
    env.HasType univs (A' :: Γ) B' (.sort v) ∧
    proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y

/-- An initial typed Pi supplies a payload with reflexive component histories. -/
theorem StageZeroPiOrigin.refl
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v)) :
    StageZeroPiOrigin D Γ A B u v (proofErase Γ A) (proofErase (A :: Γ) B) :=
  ⟨A, B, hA, hB, rfl, rfl, .refl, .refl⟩

/-- Component computation lowers through temporary prefixes without changing
stage. Context independence puts each later codomain path in the original
binder context, so appending histories requires no native image substitution. -/
theorem stage_zero_piOrigin_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    PiOriginComponentClosure (ErasedStaticStructureEtaExpansionStage D 0) Γ (StageZeroPiOrigin D Γ A B u v) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A₀, B₀, HA₀, hB₀, rfl, rfl, RA₀, RB₀⟩ := HP
  have hA₀ := HA₀.hasType.2
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
  have hΓA₀' : OnCtx (A₀.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weakN henv W⟩
  obtain ⟨A₁, HA₁, RA₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0) hΓ hΓ' W hA₀ rfl RX
  have EΓB : proofEraseCtx (A₀.liftN n :: Γ') =
      (proofErase Γ A₀).liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA₀]
  obtain ⟨B₁, HB₁, RB₁, EB₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0) hΓA₀ hΓA₀' W.succ hB₀ EΓB RY
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA₁
  have hB₁ := HB₁.hasType.2.defeqDFC henv HC
  have EB₁' := proofErase_defeqCtx hΓA₀ HC HB₁.hasType.2
  have RPB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A₀ :: Γ) B₀) (proofErase (A₀ :: Γ) B₁) :=
    RB₁.recontext_independent (fun H => H)
  rw [EB₁'] at RPB
  refine ⟨proofErase Γ A₁, proofErase (A₁ :: Γ) B₁,
    ⟨A₁, B₁, HA₀.trans HA₁, hB₁, rfl, rfl, RA₀.trans RA₁, RB₀.trans RPB⟩, EA₁.symm, ?_⟩
  rw [EB₁'] at EB₁
  exact EB₁.symm

/-- Arbitrary stage-zero computation from a typed Pi retains both component
histories at stage zero. Constant expansions, computations in their function
positions, beta interleavings and changing binder annotations are covered. -/
theorem proofErase_stage_zero_pi_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ X Y, StageZeroPiOrigin D Γ A B u v X Y ∧ ProofShape.BetaRed out (.forallE X Y) := by
  have hPi := HasType.forallE hA hB
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HC : ControlTyping (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) :=
    ⟨Γ, .forallE A B, hΓ, rfl, hPi, E⟩
  have H : Obs (StageZeroPiOrigin D Γ A B u v) 0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HC) (StageZeroPiOrigin.refl hA hB))
  have HO := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) (erased_static_structure_stage_controlObservation heq hs 0)
    (stage_zero_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero []) hPi rfl E (fun _ _ _ h => h.elim) H
  exact HO.readout

/-- A typed Pi-to-Pi path has exact component histories, including a codomain
path in the original binder context. Unlike general readout, no residual beta
step is needed at the prescribed literal endpoint. -/
theorem proofErase_stage_zero_pi_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.forallE X Y)) :
    StageZeroPiOrigin D Γ A B u v X Y := by
  have hPi := HasType.forallE hA hB
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HC : ControlTyping (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) :=
    ⟨Γ, .forallE A B, hΓ, rfl, hPi, E⟩
  have H : Obs (StageZeroPiOrigin D Γ A B u v) 0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HC) (StageZeroPiOrigin.refl hA hB))
  exact (proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (erased_static_structure_stage_controlObservation heq hs 0)
    (stage_zero_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero []) hPi
    rfl E (fun _ _ _ h => h.elim) H).literal_pi_payload

/-- Stage-zero Pi readout keeps both component paths at stage zero and in
the original scopes. This is computation readout, not extraction of component
comparisons from an arbitrary comparison of two independently supplied Pis. -/
theorem proofErase_stage_zero_pi_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    PiReadout (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, ⟨A', B', _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_stage_zero_pi_origin heq hs hΓ hA hB R
  exact ⟨X, Y, RA, by simpa only [proofEraseCtx] using RB, Rβ⟩

end Lean4Lean.VEnv.Strengthening
