import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCastResidual

/-! # Contextual full-core cast residuals

The endpoint comparison is needed only in the cast's actual context. This
allows contextual consumer certificates to justify the next cast.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Earlier-stage endpoint transport repairs arbitrary full-core reducts of a
cast at the next stage. Endpoint conversion is reconstructed from the supplied
certificate; no separate semantic equality between X and Y is assumed. -/
theorem contextual_cast_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) out) :
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ x) minor ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) (proofEraseCtx Γ) out minor := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hx
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ HC.hasType.1 R
  by_cases hp : IsProof Γ (typeCast u X Y q x)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, Ex ▸ .refl, RT.in_static_stage⟩
  · have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, x, Y, q]) HC.hasType.1 hp
    change proofErase Γ (typeCast u X Y q x) = _ at ES
    simp only [List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, _, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
    have H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a' b' :=
      HG (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    exact ⟨m', Rm, RT.in_static_stage.trans H.next_stage_full⟩

/-- The same inductive endpoint premise joins arbitrary independent core tails
of the cast and its payload at one higher finite stage. Confluence is needed
only for the level core at the original payload, never for a singleton stage. -/
theorem contextual_cast_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (RC : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) castOut)
    (RX : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ x) payloadOut) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) (proofEraseCtx Γ) castOut shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) (proofEraseCtx Γ) payloadOut shared := by
  obtain ⟨minor, RM, RR⟩ := contextual_cast_level_core_residual heq hs hl hcon hreg hoff hD
    hu hΓ hX hY hq hx HG RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hx (RM.mono (fun H => .inl H)) RX
  exact ⟨shared, RR.trans RA.in_static_stage, RB.in_static_stage⟩

end Lean4Lean.VEnv.Strengthening
