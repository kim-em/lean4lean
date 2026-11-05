import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroNativeCoherence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Returning to typed references in the full ordinary core

Postponing universe changes turns a core join into an ordinary reduction from
the reference followed by structural universe variation. If that reduction can
return, the entire join returns to the reference. Fixed ordinary-core endpoints
provide this property without purity assumptions on terms or contexts.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed reference that can return from every ordinary reduct can return
from every level-core join. The return premise is explicit and is not asserted
for arbitrary terms; fixed ordinary-core references discharge it below. -/
theorem proofErase_returning_core_join_return
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (Hreturn : ∀ {mid}, Compute (ErasedIotaPrimitive D) (proofErase Γ e) mid →
      Compute (ErasedLevelCore D) mid (proofErase Γ e))
    (HJ : ComputeJoin (ErasedLevelCore D) out (proofErase Γ e)) :
    Compute (ErasedLevelCore D) out (proofErase Γ e) := by
  obtain ⟨shared, RO, RE⟩ := HJ
  obtain ⟨mid, RM, VM⟩ := proofErase_level_core_factor hs hl hcon RE hΓ he rfl
  obtain ⟨m, HM, EM⟩ := proofErase_scoped_compute_realize
    (Step := fun _ => ErasedLevelCore D) (erased_level_core_descent hs)
    hΓ he rfl rfl (RM.scoped (fun H => .base (.inl H)))
  have V : StructuralVariant shared (proofErase Γ m) := by
    rw [EM]; exact VM.symm
  have RV : Compute (ErasedLevelCore D) shared mid := by
    simpa only [EM] using
      (proofErase_carrier_aligned_variant_level_compute V hΓ HM.hasType.2).mono
        (Step' := ErasedLevelCore D) (fun H => .inr H)
  exact RO.trans (RV.trans (Hreturn RM))

/-- Ordinary-core fixedness is sufficient for exact return from a core join.
Universe conversions are not required to be fixed. No purity or normalization
of the other endpoint, the context, or the whole environment is assumed. -/
theorem proofErase_fixed_core_join_return
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (HF : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ e))
    (HJ : ComputeJoin (ErasedLevelCore D) out (proofErase Γ e)) :
    Compute (ErasedLevelCore D) out (proofErase Γ e) :=
  proofErase_returning_core_join_return hs hl hcon hΓ he
    (fun R => by rw [HF R]; exact .refl) HJ

/-- A stage-zero tail returns to its typed ordinary-core fixed source even
in an impure context. Ordinary-core syntactic normality supplies fixedness via
NormalSyntax.fixed; the stage-zero tail may contain constant expansions. -/
theorem stage_zero_fixed_core_tail_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (HF : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ e))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    Compute (ErasedLevelCore D) out (proofErase Γ e) :=
  proofErase_fixed_core_join_return hs hl hcon hΓ he HF
    (stage_zero_compute_level_join heq hs hl hcon hc hΓ he R).symm

/-- One fixed native type is a reference for every complete stage-zero recovery
of the same typed expression. All internal native selections and final tails
may differ. Only the reference type must be fixed by ordinary computation. -/
theorem stage_zero_fixed_native_reference_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (Rref : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) reference)
    (HF : ComputeFixed (ErasedIotaPrimitive D) reference)
    (Rout : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    Compute (ErasedLevelCore D) out reference := by
  obtain ⟨P, heP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ he Rref
  obtain ⟨_, hP⟩ := heP.isType henv hΓ
  have HJ := stage_zero_native_outputs_join heq hs hl hcon hD hc hΓ he Rout Rref
  simpa only [EP] using proofErase_fixed_core_join_return hs hl hcon hΓ hP (EP ▸ HF) (EP ▸ HJ)

end Lean4Lean.VEnv.Strengthening
