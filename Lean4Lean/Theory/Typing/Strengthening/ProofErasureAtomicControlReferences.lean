import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativeReferences

/-! # Native control outputs from comparisons before instantiation

When the shared actual argument erases to an atom, a recursive comparison of
whole selected native Pis before instantiation suffices for all complete native
application outputs. This discharges the earlier post-instantiation guard premise
for literal sort control arguments. General codomain-guard coverage remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Compare all complete native application outputs from a recursive guard
on the whole selected Pis before the shared argument is substituted. The shared
argument has an atomic erasure; the original arguments and internal Pi selections
of the complete recoveries are unrestricted. No guard on the instantiated result
types is supplied. -/
theorem stage_zero_atomic_reference_application_outputs_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C U))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C) (hp : env.HasType univs Γ p C)
    (Hp : SubstitutionAtom (proofErase Γ p))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (H : LevelRecursiveGuard D mode (.forallE X Y) (.forallE Z W))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ p))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app g y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false outL outR := by
  obtain ⟨P, _, hP, EP⟩ := stage_zero_native_result_type_realize heq hs hΓ hf hp RF
  obtain ⟨Q, _, hQ, EQ⟩ := stage_zero_native_result_type_realize heq hs hΓ hg hp RG
  have JL := stage_zero_native_application_reference_join heq hs hl hcon hD hc hΓ hf hx hp RF RX RL
  have JR := stage_zero_native_application_reference_join heq hs hl hcon hD hc hΓ hg hy hp RG RY RR
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] at EP EQ JL JR
  have HC := H.pi_atomic_subst_of_joins hs hl hcon (proofErase_level_core_confluent hs hl hcon hc)
    Hp.one hΓ hP hQ EP EQ JL JR
  exact (HC.scoped (fun H => .base (.inl H))).joint.computed

namespace EnvironmentCore

/-- Literal sort control discharges atomicity and argument convergence in the
actual environment core. A recursive comparison of whole selected Pis before
instantiation compares all complete application-native outputs. Constructing
that recursive guard from an arbitrary computed selected-Pi comparison remains open. -/
theorem stage_zero_atomic_control_outputs_compare
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C U))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (H : LevelRecursiveGuard definitions mode (.forallE X Y) (.forallE Z W))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ (.app g y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) false outL outR := by
  have hp : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have EP : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have RX := stage_zero_compared_sort_returns heq sound hΓ hu (HC.symm.defeq hx) HX
  have RY := stage_zero_compared_sort_returns heq sound hΓ hu (HC.symm.defeq hy) HY
  rw [← EP] at RX RY
  exact stage_zero_atomic_reference_application_outputs_compare heq sound (levelCompatible hcon) hcon
    no_rigid (typed_core_confluence hcon) hΓ hf hg hx hy hp (by rw [EP]; exact .sort)
    RF RG H RX RY RL RR

end EnvironmentCore
end Lean4Lean.VEnv.Strengthening
