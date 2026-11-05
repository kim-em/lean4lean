import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeLevelCoreCoherence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Stage-zero native outputs and independent conversion tails

Native outputs of a fixed typed expression join in the universe-extended core.
For different expressions, a supplied core join of selected native types survives
independent stage-zero conversion tails. This does not turn an arbitrary checker
comparison into a core join or transport arbitrary comparison forward.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private stage_zero_join from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeLevelCoreCoherence
variable [Params] {D : Definitions}

/-- The existing typed level-core join theorem specialized to the full expansion
base. Constant expansions may interleave ordinary and universe computation. -/
theorem stage_zero_compute_level_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out :=
  stage_zero_join heq hs hl hcon hc hΓ he R

/-- All stage-zero native recoveries of the same typed source have an exact
common level-core reduct, including their independent final conversion tails. -/
theorem stage_zero_native_outputs_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) A)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) B) :
    ComputeJoin (ErasedLevelCore D) A B :=
  proofErase_native_mixed_level_core_coherent hs hl hcon hD hc
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (fun hΓ he R => stage_zero_compute_level_join heq hs hl hcon hc hΓ he R)
    (fun hΓ he R => stage_zero_compute_level_join heq hs hl hcon hc hΓ he R) hΓ he RL RR

/-- A native output has a typed type representative, sufficient to compose core
joins through that raw middle endpoint. No assigned-type recovery is assumed. -/
theorem stage_zero_native_output_join_trans
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) middle)
    (HL : ComputeJoin (ErasedLevelCore D) left middle)
    (HR : ComputeJoin (ErasedLevelCore D) middle right) :
    ComputeJoin (ErasedLevelCore D) left right := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ he RN
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  exact (EA ▸ HL).trans_typed hc hΓ hA (EA ▸ HR)

/-- Every stage-zero tail from a selected native type has a core join with that
type. Replay supplies its type witness independently of the assigned type. -/
theorem stage_zero_native_output_tail_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) A out) :
    ComputeJoin (ErasedLevelCore D) A out := by
  obtain ⟨P, heP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ he RN
  obtain ⟨_, hP⟩ := heP.isType henv hΓ
  simpa only [EP] using stage_zero_compute_level_join heq hs hl hcon hc hΓ hP (EP ▸ R)

/-- A core join of selected native types survives independent final conversion
paths at the expansion base. The typed expressions may differ and need not have
a common assigned type. The core-join premise is stronger than a checker check. -/
theorem stage_zero_native_output_tails_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F) (hg : env.HasType univs Γ g G)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ f) A)
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ g) B)
    (HJ : ComputeJoin (ErasedLevelCore D) A B)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) A outA)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) B outB) :
    ComputeJoin (ErasedLevelCore D) outA outB := by
  have hcl : TypedCoreConfluence (ErasedLevelCore D) := proofErase_level_core_confluent hs hl hcon hc
  have HA := stage_zero_native_output_tail_join heq hs hl hcon hc hΓ hf RF RA
  have HB := stage_zero_native_output_tail_join heq hs hl hcon hc hΓ hg RG RB
  exact stage_zero_native_output_join_trans heq hs hcl hΓ hg RG
    (stage_zero_native_output_join_trans heq hs hcl hΓ hf RF HA.symm HJ) HB

end Lean4Lean.VEnv.Strengthening
