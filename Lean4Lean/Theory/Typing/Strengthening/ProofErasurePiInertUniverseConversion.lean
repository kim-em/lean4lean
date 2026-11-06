import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierCoreConversion

/-! # Universe-directed carrier conversion

When the endpoints are types, carrier histories recover ordinary comparison,
which supports every carrier. A comparison or guarded computation exposing a
universe makes that case available even when the original carrier is hidden.
General function and structure carrier transport is not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Retained directed computation supplies a base comparison in either mode.
Its output tail is ordinary core; no guarded confluence is needed. -/
theorem PiInertInterpret.compute_compare
    (H : PiInertInterpret D n .compute Δ a b) :
    ComputedJointCompare (PiInertStage D n) Δ mode a b := by
  obtain ⟨shared, RA, RB⟩ := H.2 .refl
  exact .compute RA RB.in_pi_inert_stage (.leaf .refl)

/-- An interpreted computation between actual non-proof endpoints reflects to
definitional equality without requiring their supplied types to coincide. -/
theorem PiInertInterpret.compute_reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (H : PiInertInterpret D n .compute (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    env.IsDefEqU univs Γ a b :=
  (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H.compute_compare (mode := false)).mono (fun R => pi_inert_stage_embed R))).2 rfl hna hnb

/-- At independently sorted endpoints, the whole history can be reindexed to
any raw carrier at the same stage. The new carrier's residuals are handled by
ordinary endpoint comparison; they need not come from the old carrier. -/
theorem PiInertCarrierHistory.types_reindex
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (haC : env.HasType univs Γ a C)
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) E (proofErase Γ a) (proofErase Γ b) :=
  (H.evidence.types_checked heq hs hΓ ha hb haC).carrier_history

/-- For actual types, histories at any two assigned carriers are equivalent,
retaining all carrier residuals and future substitutions. This is a complete
carrier-conversion case for type-valued endpoints, not general term coverage. -/
theorem pi_inert_type_carrier_histories_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (haC : env.HasType univs Γ a C) (haE : env.HasType univs Γ a E) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C) (proofErase Γ a) (proofErase Γ b) ↔
      PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ E) (proofErase Γ a) (proofErase Γ b) :=
  ⟨fun H => H.types_reindex heq hs hΓ ha hb haC,
    fun H => H.types_reindex heq hs hΓ ha hb haE⟩

/-- A retained type comparison to a universe exposes sorted endpoint typings.
It converts the entire old history at its unchanged stage, independently of
the comparison's stage. No core join or reverse guarded computation is needed. -/
theorem PiInertCarrierHistory.universe_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (hv : v.WF univs)
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (HC : PiInertEvidence D k (.compare true) (proofEraseCtx Γ)
      (proofErase Γ C) (proofErase Γ (.sort v)))
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) E (proofErase Γ a) (proofErase Γ b) := by
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D k) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs k
      hΓ hΓ' W ht (pi_inert_stage_embed R)
  have hsort : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have HI := proofErase_computed_joint_types_inferred hstep hΓ hC hsort (HC.base .refl .refl)
  have HE := (proofErase_computed_joint_compare_reflect hstep hΓ hC hsort HI).2
    rfl (not_isProof_of_sort hΓ hC) (not_isProof_of_sort hΓ hsort)
  have HE := HE.of_l henv hΓ hC
  exact H.types_reindex heq hs hΓ (HE.defeq ha) (HE.defeq hb) ha

/-- Forward transport along arbitrary retained guarded computation is proved
when its output is a universe. Its stage does not inflate the old carrier
history's bound. General structural target carriers remain a separate gap. -/
theorem PiInertCarrierHistory.compute_to_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (hv : v.WF univs)
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (RC : PiInertInterpret D k .compute (proofEraseCtx Γ)
      (proofErase Γ C) (proofErase Γ (.sort v)))
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) E (proofErase Γ a) (proofErase Γ b) := by
  have hsort : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have HE := (RC.compute_reflect heq hs hΓ hC hsort
    (not_isProof_of_sort hΓ hC) (not_isProof_of_sort hΓ hsort)).of_l henv hΓ hC
  exact H.types_reindex heq hs hΓ (HE.defeq ha) (HE.defeq hb) ha

end Lean4Lean.VEnv.Strengthening
