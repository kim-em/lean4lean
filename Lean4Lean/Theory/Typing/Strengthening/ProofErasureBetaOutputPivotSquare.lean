import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFirstProjectionPivot

/-! # Expansion squares with beta evolution of selected native types

Exact preservation of every native output is too strong for dependent marked
contexts. Expansion squares only require that each selected type beta-reduce
to an output recovered at the pivot. Pi domains and structure parameters follow
that beta history, so the original expansion still has a pure beta residual.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private empty_compute_beta from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison
variable [Params] {D : PureObservation.Definitions}

/-- Every selected output may beta-reduce before it is recovered at the pivot.
Closure through arbitrary dependent contexts is still missing: a conversion
following a changed recipe needs a beta/computation square at that recipe.
This is an interface for that remaining proof, not an asserted universal law. -/
def NativeOutputBetaTransfer (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (source pivot : ProofShape) : Prop :=
  ∀ out, ScopedTypeRecovery Step Δ source out →
    ∃ shared, ScopedTypeRecovery Step Δ pivot shared ∧ ProofShape.BetaRed out shared

/-- Existing exact pivots also satisfy the weaker output-history interface. -/
theorem NativeOutputTransfer.beta_transfer (H : NativeOutputTransfer Step Δ source pivot) :
    NativeOutputBetaTransfer Step Δ source pivot :=
  fun out RN => ⟨out, H out RN, .refl⟩

/-- Output beta histories compose when pivots are advanced in sequence. -/
theorem NativeOutputBetaTransfer.trans
    (H : NativeOutputBetaTransfer Step Δ source pivot)
    (K : NativeOutputBetaTransfer Step Δ pivot target) :
    NativeOutputBetaTransfer Step Δ source target := by
  intro out RN
  obtain ⟨mid, RM, BM⟩ := H out RN
  obtain ⟨last, RL, BL⟩ := K mid RM
  exact ⟨last, RL, BM.trans BL⟩

/-- All four expansion competitors still join a historical pivot when the
selected native type changes by beta. Eta transports its domain sort to the
new domain, and structure eta transports every selected parameter. The right
residual remains pure beta, including these annotation/parameter changes. -/
theorem beta_output_pivot_expansion_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ pivot target)
    (HN : NativeOutputBetaTransfer (ErasedStaticStructureEtaExpansionUnion D) Δ source pivot)
    (Rβ : ProofShape.BetaRed source target)
    (RP : ConstantExpansion source expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original shared ∧
      ProofShape.BetaRed expanded shared := by
  rcases RP with RC | RI | RE | RS
  · cases RC
    exact ⟨_, Rbefore.trans Rafter, (constantExpansion_beta _).trans Rβ⟩
  · cases RI
    exact ⟨_, Rbefore.trans Rafter, (raw_identity_beta _ _).trans Rβ⟩
  · cases RE with
    | intro RN SD =>
      obtain ⟨out, RN', RB⟩ := HN _ RN
      obtain ⟨A', B', rfl, RA, _⟩ := beta_forallE_parts RB
      have SD' := SD.scoped_compute
        (erased_static_structure_eta_expansion_union_descent heq hs)
        (ScopedCompute.beta RA)
      have RL := static_structure_compute_under_domain heq hs SD' Rafter
      exact ⟨_, Rbefore.trans ((ScopedCompute.base
          (erased_static_structure_eta_expansion_union_eta (.intro RN' SD'))).trans
            (.lam .refl (.app RL .refl))),
        .lam RA (.app Rβ.liftN .refl)⟩
  · cases RS with
    | intro hi hx ha hp RN =>
      obtain ⟨out, RN', RB⟩ := HN _ RN
      obtain ⟨ps', rfl, RP⟩ := RB.const_spine
      refine ⟨_, Rbefore.trans ((ScopedCompute.base
        (erased_static_structure_eta_expansion_union_structure
          (.intro hi hx ha (RP.length_eq.symm.trans hp) RN'))).trans
          (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)) Rafter)), ?_⟩
      apply empty_compute_beta
      exact (nativeStructureOutput_compute
        (RP.imp (fun _ _ H => ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ) H))
        (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ) Rβ)).core_forget

/-- Nonopaque nonsort roots admit the output-history square for every union
primitive, without requiring exact preservation of the native guard. -/
theorem beta_output_pivot_primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hhead : ¬ PrimitiveHead source) (hsort : ∀ u, source ≠ .sort u)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ pivot target)
    (HN : NativeOutputBetaTransfer (ErasedStaticStructureEtaExpansionUnion D) Δ source pivot)
    (Rβ : ProofShape.BetaRed source target)
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ source expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original shared ∧
      ProofShape.BetaRed expanded shared :=
  beta_output_pivot_expansion_square heq hs Rbefore Rafter HN Rβ
    (static_structure_nonopaque_primitive hhead hsort RP)

/-- A projection over a nonopaque major uses the same output-history square.
The field may be dependent and need not be field zero. Establishing the stated
native output history through that field remains the recipe-conversion task. -/
theorem beta_output_projection_pivot_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hhead : ¬ PrimitiveHead major)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original (.proj s j pivot))
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ pivot target)
    (HN : NativeOutputBetaTransfer (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.proj s j major) (.proj s j pivot))
    (Rβ : ProofShape.BetaRed major target)
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ (.proj s j major) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original shared ∧
      ProofShape.BetaRed expanded shared :=
  beta_output_pivot_expansion_square heq hs Rbefore (.proj Rafter) HN (.proj Rβ)
    (static_structure_projection_primitive hhead RP)

end Lean4Lean.VEnv.Strengthening
