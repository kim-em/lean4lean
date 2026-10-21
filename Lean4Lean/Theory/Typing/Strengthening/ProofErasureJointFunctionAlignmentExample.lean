import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Typed function-carrier alignment without a computational join

The neutral eta obstruction persists inside a function codomain. The resulting
Pi types have no joint computational join, but all their carrier guards transfer
at the original stage by retaining the domain and replacing the neutral result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf
  types_equal native_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]
namespace FunctionCarrierAlignment

private def nativeType : VExpr := .forallE (.sort .zero) native.lift
private def assignedType : VExpr := .forallE (.sort .zero) assigned.lift
private def nativeShape : ProofShape := .forallE (.sort .zero) (nativeRaw.liftN 1)
private def assignedShape : ProofShape := .forallE (.sort .zero) (assignedRaw.liftN 1)

private theorem typed_eq : env.IsDefEq univs (context Γ) assignedType nativeType
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (.sortDF (by trivial) (by trivial) rfl) (types_equal.weak henv)

private theorem erase_types (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (context Γ) nativeType = nativeShape ∧
      proofErase (context Γ) assignedType = assignedShape := by
  have hC := context_wf hΓ
  have hC' : OnCtx (.sort .zero :: context Γ) (env.IsType univs) :=
    ⟨hC, _, HasType.sort (by trivial)⟩
  obtain ⟨EN, EA⟩ := erasures hΓ
  have ES : proofErase (context Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hC (HasType.sort (by trivial)))
  constructor
  · change proofErase (context Γ) (.forallE (.sort .zero) native.lift) = _
    rw [show proofErase (context Γ) (.forallE (.sort .zero) native.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hC typed_eq.hasType.2), ES,
      proofErase_liftN hC hC' Ctx.LiftN.one native_typed, EN]
    rfl
  · change proofErase (context Γ) (.forallE (.sort .zero) assigned.lift) = _
    rw [show proofErase (context Γ) (.forallE (.sort .zero) assigned.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hC typed_eq.hasType.1), ES,
      proofErase_liftN hC hC' Ctx.LiftN.one types_equal.hasType.1, EA]
    rfl

private theorem normal_types
    {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) (Δ) :
    NormalSyntax (Step Δ) nativeShape ∧ NormalSyntax (Step Δ) assignedShape := by
  have hv (i) : NormalSyntax (Step Δ) (.bvar i) := ⟨fun _ H => hhead H, trivial⟩
  have hs : NormalSyntax (Step Δ) (.sort .zero) := ⟨fun _ H => hhead H, trivial⟩
  have happ (i) {a} (H : NormalSyntax (Step Δ) a) : NormalSyntax (Step Δ) (.app (.bvar i) a) :=
    ⟨fun _ H => hhead H, (fun _ _ H => nomatch H), hv i, H⟩
  exact ⟨⟨(fun _ H => hhead H), hs, happ 2 (hv 3)⟩,
    ⟨(fun _ H => hhead H), hs, happ 2 ⟨(fun _ H => hhead H), hs, happ 4 (hv 0)⟩⟩⟩

/-- Actual equal typed Pi carriers with eta-different neutral codomains have no
computational join anywhere in the joint union. Nonetheless their full joint
carrier guards are equivalent at every finite stage for all raw endpoints.
There is no assumption of normalization or arbitrary type-alignment coverage. -/
theorem typed_alignment_without_join (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' T U u, OnCtx Γ' (env.IsType univs) ∧ env.IsDefEq univs Γ' T U (.sort u) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' T) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' U) shared) ∧
      ∀ stage a b, JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
          (proofErase Γ' T) a b ↔
        JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
          (proofErase Γ' U) a b := by
  obtain ⟨EN, EA⟩ := erase_types hΓ
  refine ⟨context Γ, assignedType, nativeType, _, context_wf hΓ, typed_eq, ?_, ?_⟩
  · rintro ⟨shared, RA, RN⟩
    rw [EA] at RA
    rw [EN] at RN
    have HA := scoped_normal_fixed RA (fun Δ => (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
    have HN := scoped_normal_fixed RN (fun Δ => (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
    cases HA.symm.trans HN
  · intro stage a b
    rw [EA, EN]
    have NA : NeutralResult assignedShape := .forallE (.neutral (i := 2)
      (args := [.lam (.sort .zero) (.app (.bvar 4) (.bvar 0))]))
    have NN : NeutralResult nativeShape := .forallE (.neutral (i := 2) (args := [.bvar 3]))
    constructor
    · intro H
      exact H.replace_neutral_result (result := nativeRaw.liftN 1) (erased_joint_stage_head stage) NA
    · intro H
      exact H.replace_neutral_result (result := assignedRaw.liftN 1) (erased_joint_stage_head stage) NN

end FunctionCarrierAlignment
end Lean4Lean.VEnv.Strengthening
