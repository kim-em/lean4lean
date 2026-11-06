import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionHistory

/-! # General Eq recursion from carrier histories of the indices

An Eq prefix uses carrier comparison directly. Retaining independent computation
of that carrier is essential when the full recursor spine computes. The motive
may depend on the index and its equality proof; no common reduct of the indices
or ordinary comparison between them is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- The recursive Eq-prefix rule accepts a guard at the actual index carrier,
including subsingleton and function guards that have no ordinary comparison. -/
theorem ProofShape.ComputedJointCarrierGuard.next_pi_inert_stage
    (H : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D n) Δ α a b) :
    ScopedCompute (PiInertStage D (n+1)) Δ
      (.app (ProofShape.eqRecBeforeMajor v w α a M m b) p) m := by
  have RP : ScopedCompute (PiInertStage D (n+1)) Δ (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (ProofShape.eqProofType w α a b) (m.liftN 1)) :=
    .base ⟨.inr (.inr (.inl (.intro H))), .inl trivial⟩
  apply ScopedCompute.trans (.app RP .refl)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := ProofShape.eqProofType w α a b)
      (b := m.liftN 1) (a := p)))

/-- Every full-core residual of a typed Eq recursor returns to a core residual
of its minor. Carrier history repairs all three independently computed index
positions. Both type-valued and proof-valued recursors are covered. -/
theorem pi_inert_eq_rec_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b))
    (R : Compute (ErasedLevelCore D) (proofErase Γ (eqRecApp v w α a M m b p)) out) :
    ∃ minor, Compute (ErasedLevelCore D) (proofErase Γ m) minor ∧
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) out minor := by
  obtain ⟨_, hw, hα, ha, _, _, hb, hp⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have HE := eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T ht
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht R
  by_cases hproof : IsProof Γ (eqRecApp v w α a M m b p)
  · have Em := proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hproof)
    rw [proofErase_eq_proof.2 hproof] at RM
    have E := (RM.scoped (Δ := []) (fun R => .base R)).proof_fixed
      (fun R => erased_iota_primitive_head R)
    subst mid
    exact ⟨.proof, Em ▸ .refl, RT.in_pi_inert_stage⟩
  · have Ep : proofErase Γ p = .proof := proofErase_eq_proof.2
      ⟨_, hp, HasType.eqApp heq hw hα ha hb⟩
    have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hproof
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at ES
    simp only [List.map_cons, List.map_nil, Ep] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, Rα, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
    have HG := (H (Rα.mono (fun R => .inl R)) (Ra.mono (fun R => .inl R))
      (Rb.mono (fun R => .inl R))).mono (fun R => pi_inert_stage_embed R)
    exact ⟨m', Rm.mono (fun R => .inl R),
      RT.in_pi_inert_stage.trans (ComputedJointCarrierGuard.next_pi_inert_stage HG)⟩

/-- The recursor computation retains a typed minor and an ordinary-core output
tail. The result is usable by endpoint and carrier-prefix composition. -/
theorem PiInertInterpret.eq_rec
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertInterpret D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, _, _, _, hm, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  refine ⟨⟨Γ, m, _, hΓ, rfl, hm, rfl⟩, ?_⟩
  intro out R
  obtain ⟨minor, RM, RT⟩ := pi_inert_eq_rec_core_residual heq hs hl hcon hreg hoff hD hΓ ht H R
  exact ⟨minor, RT, RM⟩

/-- General dependent Eq computation retains every future typed substitution.
Its index child is the full carrier history, rather than an ordinary comparison
or a shared-output computation certificate for the indices. -/
theorem PiInertCarrierHistory.eq_rec
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  refine ⟨PiInertInterpret.eq_rec heq hs hl hcon hreg hoff hD hΓ ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨_, _, hα, ha, _, hm, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have H' := H.substitute W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hα ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ht ES,
    ← proofErase_subst_with hΓ₀ WS hm ES, eqRecApp_subst]
  exact PiInertInterpret.eq_rec heq hs hl hcon hreg hoff hD hΓ₀
    (by simpa only [eqRecApp_subst] using ht.subst henv.orderedStrong WS hΓ₀) H'.base

end Lean4Lean.VEnv.Strengthening
