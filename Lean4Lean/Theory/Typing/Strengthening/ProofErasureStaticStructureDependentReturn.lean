import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralControlVariable

/-! # Return paths for dependent variable/universe/Pi types

The initial syntax contains variables, universes and dependent Pi binders.
Computed outputs may use the entire structure/function-eta language. Returning
the domain before the codomain preserves dependency without forward transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A dependent type skeleton whose atomic types are variables or universes.
This constrains only the initial syntax, never its computational intermediates. -/
inductive UniversePiSyntax : VExpr → Prop where
  | bvar : UniversePiSyntax (.bvar i)
  | sort : UniversePiSyntax (.sort u)
  | forallE : UniversePiSyntax A → UniversePiSyntax B → UniversePiSyntax (.forallE A B)

/-- Every enriched computation from a typed variable/universe/Pi skeleton
returns to its exact initial syntax. Dependent codomains can refer to any
original or freshly bound type variable, including proposition variables. -/
theorem static_structure_dependent_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ A (.sort u))
    (HA : UniversePiSyntax A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (proofErase Γ A) := by
  induction HA generalizing Γ u out with
  | bvar =>
    have E : proofErase Γ (.bvar _) = .bvar _ := if_neg (not_isProof_of_sort hΓ ht)
    rw [E] at R ⊢
    exact .beta (static_structure_neutral_type_variable_readout heq hs hΓ ht R)
  | @sort v =>
    exact static_structure_control_return (t := .sort v) heq hs hΓ (ht.sort_inv henv.ordered) R
  | forallE HA HB ihA ihB =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    exact static_structure_pi_return heq hs hΓ hA hB
      (fun R => ihA hΓ hA R) (fun R => ihB hΓA hB R) R

/-- All forks rooted at a typed dependent variable/universe/Pi skeleton join
at that root. Neither output needs to retain the initial syntactic form. -/
theorem static_structure_dependent_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ A (.sort u))
    (HA : UniversePiSyntax A)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared :=
  ⟨_, static_structure_dependent_return heq hs hΓ ht HA RL,
    static_structure_dependent_return heq hs hΓ ht HA RR⟩

/-- A common native certificate against a dependent variable/universe/Pi
assigned type restores that exact type. No common coverage premise is discharged. -/
theorem static_structure_exact_dependent_of_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e A)
    (HA : UniversePiSyntax A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) shared) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ A) := by
  obtain ⟨_, hA⟩ := ht.isType henv hΓ
  exact RN.convert (static_structure_dependent_return heq hs hΓ hA HA RC)

/-- Computing a dependent variable/universe/Pi binder preserves every native
body certificate forward, at the exact selected output. Body syntax and guard
depth are unrestricted; the initial binder alone satisfies the skeleton grammar. -/
theorem static_structure_dependent_forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ A C (.sort u)) (HA : UniversePiSyntax A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C))
    (ht : env.HasType univs (A :: Γ) e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have RR := static_structure_dependent_return heq hs hΓ HAC.hasType.1 HA RA
  exact proofErase_static_structure_union_recovery_backward_context heq hs hΓ HAC.symm RR ht RN

/-- Common native function and argument certificates propagate through an
application whose written domain is a dependent variable/universe/Pi type.
The function's result type and all computational intermediates are unrestricted. -/
theorem static_structure_common_dependent_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (HA : UniversePiSyntax A)
    (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) shared)
    (RNx : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) sharedX)
    (RCx : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ A) sharedX) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out :=
  static_structure_common_application heq hs hΓ hf hx hn
    (fun _ => static_structure_exact_dependent_of_common heq hs hΓ hx HA RNx RCx) RN RC

end Lean4Lean.VEnv.Strengthening
