import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreExpansion

/-! # Native recovery at an ordinary reduct of a joined assigned type

Universe postponement leaves a structural variant of an actual ordinary
reduct. Reversing that variant is a proved level-core path. Thus a native output
joined to an assigned type can recover an ordinary reduct of that assigned type,
without exact recovery of its original syntax or normalization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]
namespace LevelCoreNative

/-- A level-core native certificate at the end of a typed level-core path can
be converted to an ordinary-core reduct of the path's source. The native term
and its scope need no independent typing premise in this construction. -/
theorem pullback
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ A T)
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source out)
    (RC : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ A) out) :
    ∃ native, ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source native ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ A) native := by
  obtain ⟨native, RN, VN⟩ := proofErase_level_core_factor hs hlevels hcon RC hΓ ht rfl
  obtain ⟨A', HA, EA⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht RN
  have V : StructuralVariant out (proofErase Γ A') := by simpa only [EA] using VN.symm
  have RL := (proofErase_carrier_aligned_variant_level_compute V hΓ
    (HA.simAt hs hΓ _ ht).hasType.2).scoped (Step' := fun _ => ErasedLevelCore D)
      (Δ := Δ) (fun H => .base (.inr H))
  exact ⟨native, R.convert (by simpa only [EA] using RL), RN⟩

/-- A common level-core reduct of assigned and native types supplies a native
ordinary reduct of the assigned type. Both join branches may be nonempty. -/
theorem of_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ A T)
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source out)
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ A) out) :
    ∃ native, ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source native ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ A) native := by
  obtain ⟨shared, RA, RN⟩ := HJ
  exact pullback hs hlevels hcon hΓ ht (R.convert (RN.scoped (fun H => .base H))) RA

/-- Two level-core paths from a typed source admit a common reduct with an
ordinary residual on the right branch. Universe variation on that branch is
postponed and reversed along the left residual at a typed endpoint. -/
theorem confluent_ordinary_right
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RA : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) a)
    (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) b) :
    ∃ shared, ProofShape.Compute (ErasedLevelCore D) a shared ∧
      ProofShape.Compute (ErasedIotaPrimitive D) b shared := by
  obtain ⟨out, HA, HB⟩ := proofErase_level_core_confluent hs hlevels hcon hc hΓ ht RA RB
  obtain ⟨eb, HEB, EB⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl (RB.scoped (fun H => .base H))
  obtain ⟨shared, RC, VC⟩ := proofErase_level_core_factor hs hlevels hcon HB hΓ HEB.hasType.2 EB
  obtain ⟨ec, HEC, EC⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ HEB.hasType.2 (EB ▸ RC)
  have V : StructuralVariant out (proofErase Γ ec) := by simpa only [EC] using VC.symm
  have RL : ProofShape.Compute (ErasedLevelCore D) out (proofErase Γ ec) :=
    (proofErase_carrier_aligned_variant_level_compute V hΓ (HEC.simAt hs hΓ _ HEB.hasType.2).hasType.2).mono
      (fun H => Or.inr H)
  exact ⟨shared, HA.trans (by simpa only [EC] using RL), RC⟩

end LevelCoreNative
end Lean4Lean.VEnv.Strengthening
