import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedControlJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeControlReferenceReturn

/-! # All native selections in the compared-control obstruction

The earlier example quantified over tails from fixed selected result types.
Here every complete native recovery of each application is allowed to choose
its own intermediate types. All outputs still compare, and none of the pairs
has a core common reduct. Reference return supplies the positive comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

private theorem pure_beta_normal_core_normal (HP : PureLambda a)
    (HN : NormalSyntax (fun _ _ => False) a) : NormalSyntax (ErasedIotaPrimitive D) a := by
  induction a with
  | app f x ihf ihx =>
    exact ⟨fun _ H => HP.not_primitiveHead (erased_iota_primitive_head H), HN.2.1,
      ihf HP.1 HN.2.2.1, ihx HP.2 HN.2.2.2⟩
  | lam A b ihA ihb | forallE A b ihA ihb =>
    exact ⟨fun _ H => HP.not_primitiveHead (erased_iota_primitive_head H),
      ihA HP.1 HN.2.1, ihb HP.2 HN.2.2⟩
  | const | proj => exact HP.elim
  | bvar | sort | proof =>
    exact ⟨fun _ H => HP.not_primitiveHead (erased_iota_primitive_head H), trivial⟩

namespace EtaRecoveryJoinBoundary

/-- In the actual environment, the compared-control example admits native
recoveries on both sides and every pair of complete stage-zero native outputs
compares. No such pair has a core common reduct. Internal Pi selections and
all conversion tails are unrestricted within stage zero. This extends the
example to internal native selections; the previous theorem separately permits
higher non-eta tails from fixed outputs. It remains an example, not universal
native coherence across arbitrarily compared functions. -/
theorem compared_control_all_native_outputs_compare
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    ∃ Γ f g T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE (.sort (.succ .zero)) T) ∧
      env.HasType univs Γ g (.forallE (.sort (.succ .zero)) T) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
      (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ (.app f (.sort .zero))) out) ∧
      (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ (.app g (.sort .zero))) out) ∧
      ∀ left right,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ (.app f (.sort .zero))) left →
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ (.app g (.sort .zero))) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) false left right ∧
        ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right := by
  obtain ⟨Γ, f, g, T, _, _, L, R, hΓ, hf, hg, Hfg, _, _, _, RNL, RNR,
    HC, _, Hno, _, _, HP, HQ, HNP, HNQ, _⟩ :=
    compared_control_outputs_need_eta_join EnvironmentCore.definitions
  have hfl : env.HasType univs Γ (.app f (.sort .zero)) (T.inst (.sort .zero)) :=
    .app hf (.sort (by trivial))
  have hgr : env.HasType univs Γ (.app g (.sort .zero)) (T.inst (.sort .zero)) :=
    .app hg (.sort (by trivial))
  have HF : ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) L :=
    (pure_beta_normal_core_normal HP HNP).fixed
  have HG : ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) R :=
    (pure_beta_normal_core_normal HQ HNQ).fixed
  refine ⟨Γ, f, g, T, hΓ, hf, hg, Hfg, ⟨L, RNL⟩, ⟨R, RNR⟩, ?_⟩
  intro left right NL NR
  have RL := stage_zero_fixed_native_reference_return heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ hfl RNL HF NL
  have RR := stage_zero_fixed_native_reference_return heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ hgr RNR HG NR
  refine ⟨.compute (RL.scoped (fun H => .base (.inl H)))
    (RR.scoped (fun H => .base (.inl H))) HC, ?_⟩
  intro HJ
  have JL := stage_zero_native_outputs_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ hfl RNL NL
  have JR := stage_zero_native_outputs_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ hgr NR RNR
  have Hmiddle := stage_zero_native_output_join_trans heq EnvironmentCore.sound
    (EnvironmentCore.typed_level_core_confluence hcon) hΓ hfl NL JL HJ
  exact Hno (stage_zero_native_output_join_trans heq EnvironmentCore.sound
    (EnvironmentCore.typed_level_core_confluence hcon) hΓ hgr NR Hmiddle JR)

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
