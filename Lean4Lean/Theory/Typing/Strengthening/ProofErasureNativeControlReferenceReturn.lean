import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFixedTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeApplicationTailJoin

/-! # Comparing complete native outputs through independently chosen references

One selected Pi per function serves as a reference. Every complete native
application recovery joins its reference codomain at a shared actual argument.
Fixed reference results turn these joins into return computations, permitting
comparison without a common core reduct between the two functions' types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every complete native application output joins the instantiated codomain
of one independently chosen native Pi at a shared argument. The application's
own native Pi and all its conversion tails are extracted internally. The shared
application need not supply a native certificate of its own. -/
theorem stage_zero_native_application_reference_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) out) :
    ComputeJoin (ErasedLevelCore D) out (Y.inst (proofErase Γ p)) := by
  have hn : ¬ IsProof Γ (.app f x) := fun H => RN.ne_proof (proofErase_eq_proof.2 H)
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn] at RN
  obtain ⟨X', Y', RF', RT⟩ := RN.app_origin
  have HJ := stage_zero_native_outputs_join heq hs hl hcon hD hc hΓ hf RF' RF
  exact stage_zero_native_application_tails_join heq hs hl hcon hc hΓ hf hf hx hp hp
    RF' RF HJ RX .refl RT .refl

/-- A fixed reference codomain at the shared argument receives every complete
native output of the original application. The original argument and its
instantiated result type need not be normal or pure. -/
theorem stage_zero_fixed_native_application_reference_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (HF : ComputeFixed (ErasedIotaPrimitive D) (Y.inst (proofErase Γ p)))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) out) :
    Compute (ErasedLevelCore D) out (Y.inst (proofErase Γ p)) := by
  obtain ⟨P, _, hP, EP⟩ := stage_zero_native_result_type_realize heq hs hΓ hf hp RF
  have HJ := stage_zero_native_application_reference_join heq hs hl hcon hD hc hΓ hf hx hp RF RX RN
  simpa only [EP] using proofErase_fixed_core_join_return hs hl hcon hΓ hP (EP ▸ HF) (EP ▸ HJ)

/-- Two compared reference Pis with fixed instantiated codomains suffice to
compare arbitrary complete native outputs of two applications. Functions and
arguments may differ, and the actual recoveries need not select the reference
Pis. The assigned domain is terminal; both arguments compute to one actual
shared argument. No purity premise or core join between the references is used.
Coverage by such fixed compared references is not asserted in general. -/
theorem stage_zero_fixed_reference_application_outputs_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (HC : TerminalDomain Γ C)
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W))
    (HF : ComputeFixed (ErasedIotaPrimitive D) (Y.inst (proofErase Γ p)))
    (HG : ComputeFixed (ErasedIotaPrimitive D) (W.inst (proofErase Γ p)))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ p))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app g y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false outL outR := by
  have HI := stage_zero_terminal_native_application_types_compare heq hs hΓ hC HC hf hg hp RF RG HT
  have L := stage_zero_fixed_native_application_reference_return heq hs hl hcon hD hc hΓ hf hx hp RF HF RX RL
  have R := stage_zero_fixed_native_application_reference_return heq hs hl hcon hD hc hΓ hg hy hp RG HG RY RR
  exact .compute (L.scoped (fun H => .base (.inl H))) (R.scoped (fun H => .base (.inl H))) HI

namespace EnvironmentCore

/-- In the actual environment core, comparison of one native Pi per function
and fixed result types at the common literal sort compare every pair of complete
native control-application outputs. All core compatibility and confluence
premises are discharged. Native selections inside the supplied output
recoveries are unrestricted; purity of terms and contexts is unnecessary. -/
theorem stage_zero_fixed_reference_control_outputs_compare
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W))
    (HF : ComputeFixed (ErasedIotaPrimitive definitions) (Y.inst (.sort u)))
    (HG : ComputeFixed (ErasedIotaPrimitive definitions) (W.inst (.sort u)))
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
  rw [← EP] at RX RY HF HG
  exact stage_zero_fixed_reference_application_outputs_compare heq sound (levelCompatible hcon) hcon
    no_rigid (typed_core_confluence hcon) hΓ HC.hasType.2 (TerminalDomain.sort.convert hΓ HC)
    hf hg hx hy hp RF RG HT HF HG RX RY RL RR

end EnvironmentCore
end Lean4Lean.VEnv.Strengthening
