import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedTypeResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta

/-! # Native Pi residuals with computation and nonliteral assigned domains

A variable is declared at an identity-redex expansion of a Pi type. Its native
recovery exposes the written Pi, whose domain universe is equivalent to but
syntactically different from the assigned domain. The residual comparison is
available although exact recovery of the assigned Pi is impossible.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

private def aliasLevel : VLevel := .max (.succ .zero) .zero
private def writtenPi : VExpr := .forallE (.sort aliasLevel) (.sort .zero)
private def assignedPi : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)
private def piLevel : VLevel := .imax (.succ aliasLevel) (.succ .zero)
private def nativeType : VExpr := .app (.lam (.sort piLevel) (.bvar 0)) writtenPi

omit [Params] in
private theorem alias_equiv : aliasLevel ≈ .succ .zero := by
  simp [aliasLevel, VLevel.equiv_def, VLevel.eval]

private theorem written_type : env.HasType univs Γ writtenPi (.sort piLevel) :=
  .forallE (.sort (by trivial)) (.sort (by trivial))

private theorem written_assigned : env.IsDefEq univs Γ writtenPi assignedPi (.sort piLevel) :=
  .forallEDF (.sortDF (by trivial) (by trivial) alias_equiv) (HasType.sort (by trivial))

private theorem native_written : env.IsDefEq univs Γ nativeType writtenPi (.sort piLevel) := by
  simpa [nativeType, VExpr.inst, instVar, VExpr.lift, VExpr.liftN] using
    (IsDefEq.beta (HasType.bvar (Γ := .sort piLevel :: Γ) Lookup.zero) (written_type (Γ := Γ)))

private theorem erased_written (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ writtenPi = .forallE (.sort aliasLevel) (.sort .zero) := by
  have hdom : env.HasType univs Γ (.sort aliasLevel) (.sort (.succ aliasLevel)) := .sort (by trivial)
  have hΓD : OnCtx (.sort aliasLevel :: Γ) (env.IsType univs) := ⟨hΓ, _, hdom⟩
  rw [show proofErase Γ writtenPi = .forallE _ _ from if_neg (not_isProof_of_sort hΓ written_type),
    show proofErase Γ (.sort aliasLevel) = .sort aliasLevel from if_neg (not_isProof_of_sort hΓ hdom),
    show proofErase (.sort aliasLevel :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓD (HasType.sort (by trivial)))]

private theorem erased_assigned (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ assignedPi = .forallE (.sort (.succ .zero)) (.sort .zero) := by
  have hdom : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓD : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hdom⟩
  rw [show proofErase Γ assignedPi = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ written_assigned.hasType.2),
    show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from if_neg (not_isProof_of_sort hΓ hdom),
    show proofErase (.sort (.succ .zero) :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓD (HasType.sort (by trivial)))]

private theorem erased_native (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ nativeType =
      .app (.lam (.sort piLevel) (.bvar 0)) (.forallE (.sort aliasLevel) (.sort .zero)) := by
  have hdom : env.HasType univs Γ (.sort piLevel) (.sort (.succ piLevel)) := .sort (by trivial)
  have hΓD : OnCtx (.sort piLevel :: Γ) (env.IsType univs) := ⟨hΓ, _, hdom⟩
  have hv : env.HasType univs (.sort piLevel :: Γ) (.bvar 0) (.sort piLevel) := .bvar .zero
  have hfn := HasType.lam hdom hv
  have hn := not_isProof_of_sort hΓ (native_written (Γ := Γ)).hasType.1
  rw [show proofErase Γ nativeType = .app _ _ from if_neg hn,
    show proofErase Γ (.lam (.sort piLevel) (.bvar 0)) = .lam _ _ from
      if_neg (not_isProof_fn hΓ hfn written_type hn),
    show proofErase Γ (.sort piLevel) = .sort piLevel from if_neg (not_isProof_of_sort hΓ hdom),
    show proofErase (.sort piLevel :: Γ) (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓD hv),
    erased_written hΓ]

omit [Params] in
private theorem native_not_assigned
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) :
    ¬ ScopedCompute Step Δ
      (.app (.lam (.sort piLevel) (.bvar 0)) (.forallE (.sort aliasLevel) (.sort .zero)))
      (.forallE (.sort (.succ .zero)) (.sort .zero)) := by
  intro R
  rcases R.lambda_app_or_beta hhead with ⟨_, _, _, E, _, _⟩ | ⟨A, b, x, RF, RX, RT⟩
  · cases E
  have EF := scoped_normal_fixed RF (fun _ => ⟨fun _ H => hhead H,
    ⟨fun _ H => hhead H, trivial⟩, ⟨fun _ H => hhead H, trivial⟩⟩)
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EF
  have EX := scoped_normal_fixed RX (fun _ => ⟨fun _ H => hhead H,
    ⟨fun _ H => hhead H, trivial⟩, ⟨fun _ H => hhead H, trivial⟩⟩)
  subst x
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.Subst.cons] at RT
  have ET := scoped_normal_fixed RT (fun _ => ⟨fun _ H => hhead H,
    ⟨fun _ H => hhead H, trivial⟩, ⟨fun _ H => hhead H, trivial⟩⟩)
  cases ET

/-- In every canonical-Eq environment, native Pi exposure with a retained
comparison succeeds where exact assigned-Pi recovery fails in the full union.
The native type genuinely computes before exposing the written Pi. -/
theorem carrier_aligned_native_pi_residual_strict
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ Γ f A B T, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ f (.forallE A B) ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false T
        (proofErase Γ (.forallE A B)) ∧
      (∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
        ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
          (proofErase Γ f) (proofErase Γ (.forallE A' B')) ∧
        CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
          (proofErase Γ (.forallE A' B')) (proofErase Γ (.forallE A B))) ∧
      ¬ ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.forallE A B)) := by
  let Γ := [nativeType]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨trivial, _, native_written.hasType.1⟩
  have hl : Lookup Γ 0 nativeType := by
    simpa [Γ, nativeType, writtenPi, VExpr.lift, VExpr.liftN] using
      (Lookup.zero (Γ := []) (ty := nativeType))
  have hv : env.HasType univs Γ (.bvar 0) nativeType := .bvar hl
  have ht : env.HasType univs Γ (.bvar 0) assignedPi := (native_written.trans written_assigned).defeq hv
  have Ev : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_isProof_function_to_sort hΓ ht)
  have EO : contextOracle (proofEraseCtx Γ) 0 = proofErase Γ nativeType := by
    rw [proofEraseCtx_oracle]; exact erasedTypeOracle_valid hΓ hl
  have R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar 0)) (proofErase Γ nativeType) := by
    rw [Ev, ← EO]; exact .bvar
  have H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ nativeType) (proofErase Γ assignedPi) := by
    rw [erased_native hΓ, erased_assigned hΓ]
    apply CarrierAlignedCompare.compute (ScopedCompute.beta ?_) .refl
    · exact .base (.base (.forallE (.leaf (.sort alias_equiv)) (.leaf .refl)))
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
        ProofShape.Subst.one, ProofShape.Subst.cons] using
        (ProofShape.BetaRed.beta (A := .sort piLevel) (b := .bvar 0)
          (a := .forallE (.sort aliasLevel) (.sort .zero)))
  have residual := proofErase_carrier_aligned_recovered_pi_typed_residual
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head hΓ ht R H
  refine ⟨Γ, .bvar 0, .sort (.succ .zero), .sort .zero, proofErase Γ nativeType,
    hΓ, ht, R, H, residual, ?_⟩
  intro RX
  rw [Ev] at RX
  have RC := RX.bvar_compute
  change ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
    (contextOracle (proofEraseCtx Γ) 0) (proofErase Γ assignedPi) at RC
  rw [EO, erased_native hΓ, erased_assigned hΓ] at RC
  exact native_not_assigned erased_carrier_recovered_union_head RC

end Lean4Lean.VEnv.Strengthening
