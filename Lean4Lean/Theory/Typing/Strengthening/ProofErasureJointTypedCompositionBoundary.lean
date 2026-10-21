import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbeComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier

/-! # Typed carrier composition needs a later primitive stage

An actual empty-structure constructor is a commonly typed intermediate between
two distinct variables, all assigned the same type-valued Eq probe. Both
carrier certificates exist at stage zero, but their composite does not. At
reflexive proposition indices, stage one supplies that composite explicitly.

This refutes stage-preserving typed composition, not composition in the union
or strengthening. The input typing conversions carry information that the
primitive stage of the two certificates does not record.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier
variable [Params]

/-- A type probe cannot guard distinct bare variables at stage zero: ordinary
checking preserves variable indices and structural checking would have to
change the probe's Eq.rec head. No endpoint-conversion premise is needed. -/
theorem eqTypeProbe_zero_no_distinct_guard
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) (hne : i ≠ j) :
    ¬ JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (.bvar i) (.bvar j) := by
  intro H
  rcases H.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact hne (HC.bvar_injective (erased_joint_stage_head 0))
  exact carrier_exposure_ne_eqRec heq HB
    (eqTypeProbe_zero_head heq hregistry hRec hΓ hS hP hQ hq R)

private theorem unit_constructor_bridge
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls)) :
    env.HasType univs Γ (.const info.ctorName ls) (.const family ls) ∧
      proofErase Γ (.const info.ctorName ls) = .const info.ctorName ls ∧
      ∀ a, JointCompare Step (proofEraseCtx Γ) true (.const info.ctorName ls) a := by
  have ht := StructureReplay.structure_constructor_proofFields henv hΓ hi
    (params := []) hp.symm hx (StructureReplay.ProofFields.of_no_fields hf) hiT
  have ht : env.HasType univs Γ (.const info.ctorName ls) (.const family ls) := by
    simpa [structExpand, hf, VExpr.mkApps] using ht
  refine ⟨ht, if_neg (not_proof_at_positive_type hΓ hS ht), ?_⟩
  intro a
  have HC := JointCheck.structFields (Step := Step) (Δ := proofEraseCtx Γ) (ls := ls) hi hx
    (ps := []) hp.symm (fields := []) (hf.symm)
    (.inr (StructureReplay.ProofFields.of_no_fields hf))
    (m := a) (by intro i h; simp at h)
  exact HC

/-- All three terms have the same actual type, and both input guards are at
stage zero. Their composite is absent at zero and explicitly present at one.
The intermediate is the actual unit constructor, not an untyped raw bridge. -/
theorem joint_unit_probe_typed_composition_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j)
    (hP : env.HasType univs Γ P (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P P)) :
    ∃ B m, env.HasType univs Γ B (.sort (.succ u)) ∧
      env.HasType univs Γ (.bvar i) B ∧ env.HasType univs Γ m B ∧
      env.HasType univs Γ (.bvar j) B ∧
      JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar i)) (proofErase Γ m) ∧
      JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ m) (proofErase Γ (.bvar j)) ∧
      (¬ JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j))) ∧
      JointCarrierGuard (ErasedJointStage D 1) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  let B := eqTypeProbe (.succ u) (.const family ls) P P q
  have hB := eqTypeProbe_typed heq hΓ hS hP hP hq
  have HE := eqTypeProbe_defeq heq hΓ hS hP hP hq ⟨_, hP⟩
  obtain ⟨hm, Em, HC⟩ := unit_constructor_bridge (Step := ErasedJointStage D 0) hΓ hi hp hx hf hS hiT
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  refine ⟨B, .const info.ctorName ls, hB, HE.symm.defeq hiT, HE.symm.defeq hm,
    HE.symm.defeq hjT, ?_, ?_, ?_, ?_⟩
  · rw [Em]
    exact .carrierChecked (HC _).symm
  · rw [Em]
    exact .carrierChecked (HC _)
  · rw [Ei, Ej]
    exact eqTypeProbe_zero_no_distinct_guard heq hregistry hRec hΓ hS hP hP hq hne
  · have R := eqTypeProbe_compute_stage (stage := 0) heq hs hregistry hΓ hS hP hP hq (.leaf .refl)
    apply JointCheck.carrierCompute R
    rw [show proofErase Γ (.const family ls) = .const family ls from
      if_neg (not_isProof_of_sort hΓ hS)]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- A closed positive empty structure supplies a complete context and a
reflexive Eq major for the typed composition counterexample. The only missing
stage-zero composite is supplied at stage one. -/
theorem joint_unit_probe_typed_composition_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ B m, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ B (.sort (.succ u)) ∧
      env.HasType univs Γ (.bvar 0) B ∧ env.HasType univs Γ m B ∧
      env.HasType univs Γ (.bvar 1) B ∧
      JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 0)) (proofErase Γ m) ∧
      JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ m) (proofErase Γ (.bvar 1)) ∧
      (¬ JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1))) ∧
      JointCarrierGuard (ErasedJointStage D 1) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  let P := eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
  have hP : env.HasType univs Γ P (.sort .zero) := HasType.eqApp heq (by trivial)
    (HasType.sort (by trivial)) (HasType.sort (by trivial)) (HasType.sort (by trivial))
  have hq := HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hP
  obtain ⟨B, m, H⟩ := joint_unit_probe_typed_composition_boundary heq hs hregistry hRec
    hΓ hi hp hx hf hSΓ (HasType.bvar Lookup.zero) (HasType.bvar (.succ .zero)) (by decide) hP hq
  exact ⟨Γ, B, m, hΓ, H⟩


/-- A neutral proposition observer turns the carrier obstruction into a typed
proposition-composition obstruction. Both links and their intermediate have
literal type Prop. The composite fails at stage zero and succeeds at one. -/
theorem joint_unit_probe_proposition_composition_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j)
    (hP : env.HasType univs Γ P (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P P))
    (hl : Lookup Γ f (.forallE (eqTypeProbe (.succ u) (.const family ls) P P q) (.sort .zero))) :
    ∃ L M R, env.HasType univs Γ L (.sort .zero) ∧
      env.HasType univs Γ M (.sort .zero) ∧ env.HasType univs Γ R (.sort .zero) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ M) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ M) (proofErase Γ R) ∧
      (¬ JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ R)) ∧
      JointCompare (ErasedJointStage D 1) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ R) := by
  let B := eqTypeProbe (.succ u) (.const family ls) P P q
  have hB := eqTypeProbe_typed heq hΓ hS hP hP hq
  have HE := eqTypeProbe_defeq heq hΓ hS hP hP hq ⟨_, hP⟩
  obtain ⟨hm, Em, HC⟩ := unit_constructor_bridge (Step := ErasedJointStage D 0) hΓ hi hp hx hf hS hiT
  have hfun : env.HasType univs Γ (.bvar f) (.forallE B (.sort .zero)) := .bvar hl
  have hL : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort .zero) := hfun.app (HE.symm.defeq hiT)
  have hM : env.HasType univs Γ (.app (.bvar f) (.const info.ctorName ls)) (.sort .zero) := hfun.app (HE.symm.defeq hm)
  have hR : env.HasType univs Γ (.app (.bvar f) (.bvar j)) (.sort .zero) := hfun.app (HE.symm.defeq hjT)
  have Ef : proofErase Γ (.bvar f) = .bvar f := if_neg (not_isProof_function_to_sort hΓ hfun)
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  have EL : proofErase Γ (.app (.bvar f) (.bvar i)) = .app (.bvar f) (.bvar i) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hL), Ef, Ei]
  have EM : proofErase Γ (.app (.bvar f) (.const info.ctorName ls)) = .app (.bvar f) (.const info.ctorName ls) := by
    rw [show proofErase Γ (.app (.bvar f) (.const info.ctorName ls)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hM), Ef, Em]
  have ER : proofErase Γ (.app (.bvar f) (.bvar j)) = .app (.bvar f) (.bvar j) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar j)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hR), Ef, Ej]
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hPi := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have EPi : proofErase Γ (.forallE B (.sort .zero)) = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))]
  have HO : contextOracle (proofEraseCtx Γ) f = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl, EPi]
  refine ⟨_, _, _, hL, hM, hR, ?_, ?_, ?_, ?_⟩
  · rw [EL, EM]
    exact .app (.leaf .refl) (HC _).symm
  · rw [EM, ER]
    exact .app (.leaf .refl) (HC _)
  · rw [EL, ER]
    intro H
    exact eqTypeProbe_zero_no_distinct_guard heq hregistry hRec hΓ hS hP hP hq hne
      (H.bvar_app_carrier (erased_joint_stage_head 0) HO)
  · rw [EL, ER]
    apply (JointCompare.bvar_app_iff (erased_joint_stage_head 1) HO).2
    apply JointCheck.carrierCompute (eqTypeProbe_compute_stage (stage := 0) heq hs hregistry hΓ hS hP hP hq (.leaf .refl))
    rw [show proofErase Γ (.const family ls) = .const family ls from if_neg (not_isProof_of_sort hΓ hS)]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- The proposition obstruction has an actual well-formed three-variable
context whenever a closed positive empty structure is available. No assumed
endpoint equality, ill-typed middle, or fresh Eq proof is used in this witness. -/
theorem joint_unit_probe_proposition_composition_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ L M R, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ L (.sort .zero) ∧
      env.HasType univs Γ M (.sort .zero) ∧ env.HasType univs Γ R (.sort .zero) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ M) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ M) (proofErase Γ R) ∧
      (¬ JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ R)) ∧
      JointCompare (ErasedJointStage D 1) (proofEraseCtx Γ) true (proofErase Γ L) (proofErase Γ R) := by
  let S := VExpr.const family ls
  let P := eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
  have hP : env.HasType univs [] P (.sort .zero) := HasType.eqApp heq (by trivial)
    (HasType.sort (by trivial)) (HasType.sort (by trivial)) (HasType.sort (by trivial))
  let q := eqReflApp (.succ .zero) (.sort .zero) P
  have hq : env.HasType univs [] q (eqApp (.succ .zero) (.sort .zero) P P) :=
    HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hP
  let B := eqTypeProbe (.succ u) S P P q
  have hB := eqTypeProbe_typed heq (Γ := []) trivial hS hP hP hq
  let F := VExpr.forallE B (.sort .zero)
  have hF : env.HasType univs [] F (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallE hB (.sort (by trivial))
  let Γ := [S, S, F]
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hF⟩, _, hS.weak0 henv.ordered⟩, _, hS.weak0 henv.ordered⟩
  have hl : Lookup Γ 2 (.forallE B (.sort .zero)) := .succ (.succ .zero)
  obtain ⟨L, M, R, H⟩ := joint_unit_probe_proposition_composition_boundary heq hs hregistry hRec
    hΓ hi hp hx hf (hS.weak0 henv.ordered) (HasType.bvar Lookup.zero) (HasType.bvar (.succ .zero))
    (by decide) (hP.weak0 henv.ordered) (hq.weak0 henv.ordered) hl
  exact ⟨Γ, L, M, R, hΓ, H⟩

end Lean4Lean.VEnv.Strengthening
