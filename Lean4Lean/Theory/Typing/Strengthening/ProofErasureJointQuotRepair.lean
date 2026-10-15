import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotBoundary
import Lean4Lean.Theory.Typing.Strengthening.QuotHeadComputation

/-! # Restoring quotient-prefix coverage in erased joint computation

The already proved closed Quot.lift equation supplies the missing computation.
It can be added to the parameterized core without changing the joint grammar.
This repairs the quotient witness, not the unrestricted re-synthesis law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation
variable [Params]
namespace ErasedQuotCore

/-- All stored equations and selected structure programs, now including the
proved closed proposition-source Quot.lift equation. -/
noncomputable def definitions (hq : QuotRegistered env) : Definitions :=
  RegisteredStructure.definitions (ClosedQuot.definitions env univs henv hq)

/-- The added equation is sound in every context; it uses no strengthening. -/
theorem sound (hq : QuotRegistered env) : (definitions hq).Sound env univs :=
  RegisteredStructure.definitions_sound (ClosedQuot.definitions_sound henv hq)

/-- Every previous core equation remains available in the repaired collection. -/
theorem includes_core (hq : QuotRegistered env)
    (H : ErasedCore.definitions.unfolds c ls rhs) : (definitions hq).unfolds c ls rhs := by
  rcases H with H | H
  · exact .inl (.inl H)
  · exact .inr H

/-- Every actual proposition-source quotient prefix has exact forward erasure
already at stage zero. Unlike singleton family guards, this needs no recursive
comparison certificate or re-synthesis premise. -/
theorem quotient_prefix_forward (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (H : QuotPrefixUnfold env univs Γ levels args rhs) :
    ProofShape.ScopedCompute (ErasedJointStage (definitions hq) 0) (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const ``Quot.lift levels) args)) (proofErase Γ rhs) := by
  have R := (ClosedQuot.prefix_compute henv hq H).of_inclusion (D' := ErasedQuotCore.definitions hq) (fun _ _ _ H => Or.inl H)
  have R' : PatternCompute (definitions hq) (mkApps (.const ``Quot.lift levels) args) rhs := .base (.base R)
  exact (proofErase_pattern_compute_forward (sound hq) hcon hΓ ht R').scoped (fun H => .base H)

end ErasedQuotCore

namespace JointQuotBoundary
open private context source context_wf source_typed source_eq_sort erased_source core_no_quot
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotBoundary

private theorem source_compute (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    Compute (ErasedQuotCore.definitions hq) source (.sort .zero) := by
  have hΓ := context_wf heq hq
  have ht := source_typed hq
  obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
  have HP := QuotPrefixUnfold.atFive henv hΓ hq (by trivial) (by trivial) (by rfl) ⟨_, hf⟩
  have R := (ClosedQuot.prefix_compute henv hq HP).of_inclusion (D' := ErasedQuotCore.definitions hq) (fun _ _ _ H => Or.inl H)
  apply Compute.trans (Compute.app R .refl)
  apply Compute.of_beta
  apply VExpr.BetaRed.trans .beta
  simp only [VExpr.inst, VExpr.lift, VExpr.liftN, instVar]
  exact .beta

/-- The same typed source that is stuck at every old joint stage computes to
Prop at repaired stage zero. This is an exact checked repair of the omission,
not a claim of complete sort exposure for the enlarged core. -/
theorem repaired_sort_witness (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    ∃ Γ T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ T (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ T (.sort .zero) (.sort (.succ .zero)) ∧
      ProofShape.ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
        (proofEraseCtx Γ) (proofErase Γ T) (.sort .zero) ∧
      ∀ n Δ w, ¬ ProofShape.ScopedCompute (ErasedJointUnion ErasedCore.definitions) Δ
        ((proofErase Γ T).liftN n) (.sort w) := by
  have hΓ := context_wf heq hq
  have ht := source_typed hq
  refine ⟨context, source, hΓ, ht, source_eq_sort heq hq, ?_, ?_⟩
  · have R : PatternCompute (ErasedQuotCore.definitions hq) source (.sort .zero) :=
      .base (.base (source_compute heq hq))
    have R' := proofErase_pattern_compute_forward (ErasedQuotCore.sound hq) hcon hΓ ht R
    rw [show proofErase context (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))] at R'
    exact R'.scoped (fun H => .base H)
  · intro n Δ w R
    obtain ⟨args, hlen, hs, E⟩ := erased_source heq hq
    rw [E] at R
    simp only [ProofShape.liftN, ProofShape.liftN_mkApps] at R
    obtain ⟨stage, R⟩ := R.finite_stage erased_joint_stage_mono
    have H := fixed hq (fun _ _ => core_no_quot hq)
      (by simpa only [List.length_map] using hlen)
      (by intro a ha; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha; exact (hs b hb).liftN) R
    cases H

end JointQuotBoundary
end Lean4Lean.VEnv.Strengthening
