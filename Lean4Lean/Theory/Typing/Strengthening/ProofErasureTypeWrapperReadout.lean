import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeControlCuts
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaPrimitiveResidual

/-! # Arbitrary computation after administrative wrappers of a type

Constant and natively annotated identity wrappers preserve a marked type
payload. Full-union computation may change their annotations, expand their
functions, and introduce further control frames. The resulting observation
beta-reads a forward computation of the original type. The pure beta residual
is stronger than mutual reachability of the wrappers and their payloads.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.TypeArgumentObservation
variable [Params] {D : PureObservation.Definitions}

/-- Administrative root expansions whose beta contraction returns their
source. Identity annotations require an actual native certificate at creation;
this relation does not include arbitrary reverse beta steps or type casts. -/
def TypeWrapperExpansion (D : PureObservation.Definitions) (Δ : List ProofShape)
    (a b : ProofShape) : Prop :=
  ConstantExpansion a b ∨ NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ a b

/-- Each administrative expansion is an actual full-union computation. -/
theorem TypeWrapperExpansion.compute (H : TypeWrapperExpansion D Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b := by
  rcases H with H | H
  · exact .base ⟨0, .inr H⟩
  · exact .base (erased_static_structure_eta_expansion_union_identity H)

/-- Each administrative expansion beta-contracts to its source, independently
of any later computation or retained native recovery. -/
theorem TypeWrapperExpansion.beta_reverse (H : TypeWrapperExpansion D Δ a b) : BetaRed b a := by
  rcases H with H | H
  · cases H
    exact constantExpansion_beta _
  · cases H with
    | intro _RN =>
      rename_i annotation
      simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
        ProofShape.liftN_zero] using (BetaRed.beta (A := annotation) (b := .bvar 0) (a := a))

private theorem wrapper_compute
    (H : ReflTransGen (TypeWrapperExpansion D Δ) a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b := by
  induction H with
  | rfl => exact .refl
  | tail _ H ih => exact ih.trans H.compute

private theorem wrapper_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : ReflTransGen (TypeWrapperExpansion D Δ) a b)
    (H : Obs P n Δ S a t o) : Obs P n Δ S b t o := by
  induction W with
  | rfl => exact H
  | tail _ W ih =>
    rcases W with W | W
    · cases W
      exact ih.constant_expansion
    · exact ih.native_identity (erased_static_structure_eta_expansion_union_descent heq hs) W

/-- Arbitrary full-union computation after any finite nesting of constant
and native identity wrappers beta-reads a computed representative of the original
type. This includes computation inside the frames and after their contraction,
not merely component rounds before beta. No HJ or fork-joining premise is used. -/
theorem static_structure_type_wrappers_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (W : ReflTransGen (TypeWrapperExpansion D (proofEraseCtx Γ)) (proofErase Γ A) wrapped)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) wrapped out) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧ BetaRed out (proofErase Γ A') := by
  have HT : ControlTyping (proofEraseCtx Γ) (proofErase Γ A) (.sort u) :=
    ⟨Γ, A, hΓ, rfl, hA, rfl⟩
  have H : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ A) (.sort u) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HT) (TypeArgumentOrigin.refl hA))
  have HW := wrapper_observation heq hs W H
  obtain ⟨e, HE, Ee⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl (wrapper_compute W)
  exact static_structure_type_payload_program_readout heq hs hΓ HE.hasType.2
    (Ee.symm ▸ HW) (Ee.symm ▸ R)

/-- A primitive at a type-valued literal beta redex can only introduce a
constant or native identity wrapper. Arbitrary computation after that expansion
beta-reads a computation of the original redex. The original beta contraction
has not been performed by this theorem; general beta stripping remains open. -/
theorem static_structure_type_beta_root_expansion_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort u))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) wrapped)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) wrapped out) :
    ∃ e', env.IsDefEq univs Γ (.app (.lam A b) x) e' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A b) x)) (proofErase Γ e') ∧ BetaRed out (proofErase Γ e') := by
  have hn := not_isProof_of_sort hΓ ht
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  have hnf := not_isProof_fn hΓ hf hx hn
  have EE : proofErase Γ (.app (.lam A b) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A b) x) = .app _ _ from if_neg hn,
      show proofErase Γ (.lam A b) = .lam _ _ from if_neg hnf]
  have HC : ControlTyping (proofEraseCtx Γ) (proofErase Γ (.app (.lam A b) x)) (.sort u) :=
    ⟨Γ, _, hΓ, rfl, ht, rfl⟩
  have HW : TypeWrapperExpansion D (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) wrapped := by
    have H := static_structure_beta_redex_primitive (EE ▸ RP)
    rw [← EE] at H
    rcases H with H | H | H | H
    · exact .inl H
    · exact .inr H
    · exact (HC.no_eta_sort (erased_static_structure_eta_expansion_union_descent heq hs) H).elim
    · exact (HC.no_masked_structure (erased_static_structure_eta_expansion_union_descent heq hs) H).elim
  exact static_structure_type_wrappers_readout heq hs hΓ ht (.tail .rfl HW) R

end Lean4Lean.VEnv.Strengthening
