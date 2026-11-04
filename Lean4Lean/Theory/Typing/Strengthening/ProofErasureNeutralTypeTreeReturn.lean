import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureTypeArgumentOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Return trees with nested neutral type constructors

Universe-to-universe variables may be applied recursively to arbitrary members
of the tree. Dependent Pi components may use the same constructors. The return
property constrains only initial syntax, not any computed intermediate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A typed return tree contains universes, opaque type variables, dependent
Pis and recursively nested neutral universe-to-universe applications. This
does not classify all types: arbitrary data-indexed families are excluded. -/
inductive NeutralTypeTree : List VExpr → VExpr → VLevel → Prop where
  | sort : u.WF univs → NeutralTypeTree Γ (.sort u) (.succ u)
  | bvar : env.HasType univs Γ (.bvar i) (.sort u) → NeutralTypeTree Γ (.bvar i) u
  | forallE : NeutralTypeTree Γ A u → NeutralTypeTree (A :: Γ) B v →
      NeutralTypeTree Γ (.forallE A B) (.imax u v)
  | app : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)) →
      NeutralTypeTree Γ A u → NeutralTypeTree Γ (.app (.bvar f) A) v

/-- Every tree carries ordinary typing at its indexed universe. -/
theorem NeutralTypeTree.typed (H : NeutralTypeTree Γ A u) : env.HasType univs Γ A (.sort u) := by
  induction H with
  | sort hu => exact .sort hu
  | bvar h => exact h
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | app hf _ ih => exact hf.app ih

/-- All computations from a return tree return to its exact original type.
The application case reads the complete argument history and uses its recursive
return theorem; it imposes no shape condition on the computed argument. -/
theorem NeutralTypeTree.compute_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NeutralTypeTree Γ A u) (hΓ : OnCtx Γ (env.IsType univs))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out (proofErase Γ A) := by
  induction H generalizing out with
  | sort hu => exact static_structure_control_return (t := .sort _) heq hs hΓ hu R
  | bvar ht => exact static_structure_dependent_return heq hs hΓ ht .bvar R
  | forallE HA HB ihA ihB =>
    exact static_structure_pi_return heq hs hΓ HA.typed HB.typed
      (fun R => ihA hΓ R) (fun R => ihB ⟨hΓ, _, HA.typed⟩ R) R
  | @app Γ f u v A hf HA ih =>
    have ht := hf.app HA.typed
    have E : proofErase Γ (.app (.bvar f) A) = .app (.bvar f) (proofErase Γ A) := by
      rw [show proofErase Γ (.app (.bvar f) A) = .app _ _ from
        if_neg (not_isProof_of_sort hΓ ht),
        show proofErase Γ (.bvar f) = .bvar f from if_neg (not_isProof_function_to_sort hΓ hf)]
    rw [E] at R ⊢
    obtain ⟨_, _, RA, RB⟩ := static_structure_neutral_type_argument_origin heq hs hΓ HA.typed hf R
    exact (ScopedCompute.beta RB).trans (.app .refl (ih hΓ RA))

/-- Common native evidence at any return-tree assignment meets the exact
assigned-type demand for retained values. Coverage itself is not asserted. -/
theorem CommonNativeArgument.exact_neutral_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : NeutralTypeTree Γ A u) (hΓ : OnCtx Γ (env.IsType univs))
    (H : CommonNativeArgument D Γ x A) (hn : ¬ IsProof Γ x) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A) := by
  obtain ⟨shared, RN, RC⟩ := H hn
  exact RN.convert (HT.compute_return heq hs hΓ RC)

/-- A computed binder originating at a return tree admits exact forward
native transport. The body and its selected native output are unrestricted. -/
theorem NeutralTypeTree.forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : NeutralTypeTree Γ A u) (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ A C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C))
    (ht : env.HasType univs (A :: Γ) e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out :=
  proofErase_static_structure_union_recovery_backward_context heq hs hΓ HAC.symm
    (HT.compute_return heq hs hΓ RA) ht RN

/-- Beta at a commonly recovered argument assigned a return tree preserves
every selected native result, including its final conversion tail. -/
theorem NeutralTypeTree.beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : NeutralTypeTree Γ A u) (hΓ : OnCtx Γ (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HX : CommonNativeArgument D Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out :=
  static_structure_root_beta_native_recovery heq hs hΓ HT.typed hb hx
    (HX.exact_neutral_tree heq hs HT hΓ) RN

end Lean4Lean.VEnv.Strengthening
