import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverySubstitutionBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCarrierApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKExample

/-! # Contextual recovery repairs the neutral-unit type obstruction

A variable declared at the unit-index Eq recursor acquires a Pi recovery at
structure stage one. No old compared-K stage can recover any Pi for that same
variable. This is a strict coverage witness, not recovery completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private core_no_rigid core_no_eqRec from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKExample
variable [Params]

private theorem erase_type_arrow (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) =
      .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) := by
  have hPi : env.HasType univs Γ (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
      (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
    .forallE (.sort (by trivial)) (.sort (by trivial))
  have hΓT : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [show proofErase Γ (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) =
    .forallE (proofErase Γ (.sort (.succ .zero)))
      (proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero))) from
      if_neg (not_isProof_of_sort hΓ hPi)]
  rw [show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
    show proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
    if_neg (not_isProof_of_sort hΓT (HasType.sort (by trivial)))]

/-- The neutral-unit obstruction separates actual recovery certificates: the
same typed variable recovers a Pi at contextual structure stage one, but at no
old compared-K stage. Both sides use the same equation collection. -/
theorem unit_neutral_scoped_recovery_separation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family levels) (.sort (.succ u)))
    (hD : ∀ c ∈ [family, ``Eq, ``Eq.rec], ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.bvar 0) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ProofShape.ScopedTypeRecovery (ErasedStructureSingletonStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.bvar 0)) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ∀ stage A B, ¬ ProofShape.TypeRecovery (ErasedComparedKStage D stage)
        (ProofShape.contextOracle (proofEraseCtx Γ)) (proofErase Γ (.bvar 0)) (.forallE A B) := by
  obtain ⟨Γ, e, hΓ, he, HE, RC, HN⟩ := unit_neutral_pi_exposure_separation
    heq hreg hoff hi hp hx hf hS hD
  let F := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  have hΓe : OnCtx (e :: Γ) (env.IsType univs) := ⟨hΓ, _, he⟩
  have hv : env.HasType univs (e :: Γ) (.bvar 0) e.lift := .bvar .zero
  have hvF : env.HasType univs (e :: Γ) (.bvar 0) F := (HE.weak henv).defeq hv
  have hn := not_proof_at_positive_type hΓe (he.weak henv) hv
  have RC' : ProofShape.ScopedCompute (ErasedStructureSingletonStage D 1) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ F) := by
    rw [erase_type_arrow hΓ]
    exact RC.mono (erased_unit_singleton_into_structure 1)
  have RW := proofErase_scoped_compute_weak' (erased_structure_singleton_stage_subst heq hs 1)
    hΓ hΓe (Ctx.Lift'.skip .refl) he HE.hasType.2 RC'
  have RW' : ProofShape.ScopedCompute (ErasedStructureSingletonStage D 1) (proofEraseCtx (e :: Γ))
      (proofErase (e :: Γ) e.lift) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by
    simpa only [← lift_eq_lift', F, VExpr.lift, VExpr.liftN, erase_type_arrow hΓe] using RW
  refine ⟨e :: Γ, hΓe, hvF, proofErase_scoped_lookup_recovery hΓe Lookup.zero hn RW', ?_⟩
  intro stage A B HR
  rw [show proofErase (e :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at HR
  have HC := HR.bvar_compute
  change ProofShape.Compute (ErasedComparedKStage D stage) ((proofErase Γ e).liftN 1) (.forallE A B) at HC
  have H := HC.subst (erased_compared_K_stage_subst stage) (σ := ProofShape.Subst.id.cons .proof)
  simp only [ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.subst] at H
  exact HN stage _ _ H


omit [Params] in
/-- The strict recovery improvement holds for the actual core containing all
stored definitions and selected structure equations, in any canonical-Eq
environment with a positive closed empty structure. -/
theorem canonical_unit_scoped_recovery_separation {env : VEnv} (henv : env.WF)
    (U : Nat) (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType U [] (.const family levels) (.sort (.succ u))) :
    letI := henv.params U
    ∃ Γ, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ (.bvar 0) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ProofShape.ScopedTypeRecovery (ErasedStructureSingletonStage ErasedCore.definitions 1)
        (proofEraseCtx Γ) (proofErase Γ (.bvar 0))
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ∀ stage A B, ¬ ProofShape.TypeRecovery (ErasedComparedKStage ErasedCore.definitions stage)
        (ProofShape.contextOracle (proofEraseCtx Γ)) (proofErase Γ (.bvar 0)) (.forallE A B) := by
  letI := henv.params U
  obtain ⟨data, hreg, _, _, hoff, _⟩ := heq.recursorRegistration henv
  apply unit_neutral_scoped_recovery_separation heq
    (RegisteredStructure.definitions_sound (PureObservation.Definitions.ofEnv_sound henv))
    hreg hoff hi hp hx hf hS
  intro c hc levels rhs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact core_no_rigid (henv.projectionRigid hi)
  · exact core_no_rigid (heq.rigid henv)
  · exact core_no_eqRec heq


/-- Contextual computation does not restore exact selected-type substitution.
For any recovery computation admitting descent, the lifted identity cannot
recover the captured Pi annotation containing the newly inserted proposition.
This explains why the joint law must still choose new domain representatives. -/
theorem scoped_identity_captured_not_recovered
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ProofShape.ScopedTypeRecovery Step (proofEraseCtx (.sort .zero :: Γ))
      (proofErase (.sort .zero :: Γ) (Developments.ident 0).lift)
      (proofErase (.sort .zero :: Γ) (EtaScope.capturedPi (.sort .zero))) := by
  intro R
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [proofErase_liftN hΓ hΓS Ctx.LiftN.one
    (Developments.ident_typed env univs Γ 0)] at R
  obtain ⟨A, _, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓS Ctx.LiftN.one
    (Developments.ident_typed env univs Γ 0) rfl R
  rw [ErasedRecoverySubstitutionBoundary.captured_erasure hΓ] at EA
  apply ErasedRecoverySubstitutionBoundary.captured_not_thinned (proofErase Γ A)
  simpa only [← ProofShape.lift'_consN_skipN, Lift.consN, Lift.skipN] using EA

end Lean4Lean.VEnv.Strengthening
