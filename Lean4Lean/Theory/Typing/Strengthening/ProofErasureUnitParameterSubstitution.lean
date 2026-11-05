import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedNativeSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorParameterBoundary

/-! # Dependent body repair despite impossible exact argument recovery

In the retained-parameter counterexample, compute both ambient unit variables
and the constructor parameter together. The final simultaneous images recover
their transformed assigned types, so arbitrary generic body histories join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- The simultaneous endpoint replaces the body argument and both ambient
unit variables. Variables outside the three-slot source context are unchanged
relative to single instantiation. -/
def unitParameterImages (unitCtor ctor : Name) : ProofShape.Subst
  | 0 => .app (.const ctor []) (.const unitCtor [])
  | 1 => .const unitCtor []
  | 2 => .const unitCtor []
  | i + 3 => .bvar (i + 2)

private def unitParameterTerms (unitCtor ctor : Name) : VExpr.Subst
  | 0 => .app (.const ctor []) (.const unitCtor [])
  | 1 => .const unitCtor []
  | 2 => .const unitCtor []
  | i + 3 => .bvar (i + 2)

/-- Every full computation of an arbitrary dependent body instantiates up to
an explicit join in the retained-parameter boundary configuration. The old
argument is mk p at assigned type Tag q; it has no exactly recoverable future
image. Computing p and q along with mk p nevertheless repairs the whole body
history. No type-fork, common-coverage or forward-binder premise is assumed. -/
theorem static_structure_unit_parameter_body_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero))))
    (hb : env.HasType univs
      [.app (.const t []) (.bvar 0), .const s [], .const s []] b B)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx [.app (.const t []) (.bvar 0), .const s [], .const s []])
      (proofErase [.app (.const t []) (.bvar 0), .const s [], .const s []] b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx [.const s [], .const s []])
        (proofErase [.const s [], .const s []] (b.inst (.app (.const c []) (.bvar 1))))
        (out.subst (unitParameterImages info.ctorName c)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx [.const s [], .const s []])
        (out.inst (.app (.const c []) (.bvar 1)))
        (out.subst (unitParameterImages info.ctorName c)) := by
  let S := VExpr.const s []
  let Γ := [S, S]
  let A := VExpr.app (.const t []) (.bvar 0)
  let x := VExpr.app (.const c []) (.bvar 1)
  let z := VExpr.const info.ctorName []
  let y := VExpr.app (.const c []) z
  let σ := unitParameterTerms info.ctorName c
  let τ := unitParameterImages info.ctorName c
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hP : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hQ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hZ : env.HasType univs Γ z S :=
    hP.unitLike_constructor henv hΓ hi (params := []) hp.symm hx hz
  have hC : env.HasType univs [] (.const c [])
      (.forallE S (.app (.const t []) (.bvar 0))) :=
    .const (henv.ordered.projectionConstructor hTag) (by simp) rfl
  have hA : env.HasType univs Γ A (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hQ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hX₀ : env.HasType univs Γ x (.app (.const t []) (.bvar 1)) :=
    .app (hC.weak0 henv.ordered) hP
  have hX : env.HasType univs Γ x A :=
    (IsDefEq.appDF (hF.weak0 henv.ordered)
      (IsDefEq.unitLike hi (params := []) hp.symm hx hz hP hQ)).defeq hX₀
  have hY : env.HasType univs Γ y (.app (.const t []) z) :=
    .app (hC.weak0 henv.ordered) hZ
  have hnZ := not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hZ
  have hnX := not_proof_at_positive_type hΓ hA hX
  have hnY := not_proof_at_positive_type hΓ (HasType.app (hF.weak0 henv.ordered) hZ) hY
  have EZ : proofErase Γ z = .const info.ctorName [] := if_neg hnZ
  have EP : proofErase Γ (.bvar 1) = .bvar 1 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hP)
  have EX : proofErase Γ x = .app (.const c []) (.bvar 1) := by
    simpa [VExpr.mkApps, ProofShape.mkApps, EP] using
      proofErase_const_spine (c := c) (ls := []) (args := [.bvar 1]) hΓ hX hnX
  have EY : proofErase Γ y = .app (.const c []) (.const info.ctorName []) := by
    simpa [VExpr.mkApps, ProofShape.mkApps, EZ] using
      proofErase_const_spine (c := c) (ls := []) (args := [z]) hΓ hY hnY
  have EA : proofErase Γ A = .app (.const t []) (.bvar 0) := by
    have EQ : proofErase Γ (.bvar 0) = .bvar 0 :=
      if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hQ)
    simpa [VExpr.mkApps, ProofShape.mkApps, EQ] using
      proofErase_const_spine (c := t) (ls := []) (args := [.bvar 0]) hΓ hA (not_isProof_of_sort hΓ hA)
  have W : Ctx.SubstEq env univs Γ σ σ (A :: Γ) := by
    exact .cons (.cons (.cons .nil hS hZ) (hS.weak0 henv.ordered) hZ) hA hY
  have E : ErasedSubstAgreement (A :: Γ) Γ σ τ := by
    intro i T hl _
    dsimp [Γ] at hl
    cases hl with
    | zero => exact EY
    | succ hl => cases hl with
      | zero => exact EZ
      | succ hl => cases hl with
        | zero => exact EZ
        | succ hl => cases hl
  have NZ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.const info.ctorName []) (.const s []) := by
    have H := proofErase_structure_constructor_native (args := []) (levels := [])
      (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hi hx (by simp [hp, hz]) hZ hnZ
    simp only [List.take_nil, List.map_nil, VExpr.mkApps, List.foldl_nil, ProofShape.mkApps] at H
    change ScopedTypeRecovery _ _ (proofErase Γ z) (.const s []) at H
    rwa [EZ] at H
  have NY : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.const info.ctorName [])) (.app (.const t []) (.const info.ctorName [])) := by
    have H := proofErase_structure_constructor_native (args := [z]) (levels := [])
      (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hTag rfl rfl hY hnY
    change ScopedTypeRecovery _ _ (proofErase Γ y) (.app (.const t []) (proofErase Γ z)) at H
    rwa [EY, EZ] at H
  have ES₀ : proofErase [S] S = .const s [] :=
    if_neg (not_isProof_of_sort (show OnCtx [S] (env.IsType univs) from ⟨trivial, _, hS⟩)
      (hS.weak0 henv.ordered))
  have ESempty : proofErase [] S = .const s [] := if_neg (not_isProof_of_sort (by trivial) hS)
  have HI : NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D) (A :: Γ) Γ τ := by
    intro i T hl _
    dsimp [Γ] at hl
    cases hl with
    | zero => simpa [proofEraseCtx, contextOracle, TypeOracle.cons, EA,
        ProofShape.liftN, ProofShape.subst, τ, unitParameterImages] using NY
    | succ hl => cases hl with
      | zero => simpa [proofEraseCtx, contextOracle, TypeOracle.cons, Γ, ES₀, ESempty,
          ProofShape.liftN, ProofShape.subst, τ, unitParameterImages] using NZ
      | succ hl => cases hl with
        | zero => simpa [proofEraseCtx, contextOracle, TypeOracle.cons, Γ, ES₀, ESempty,
            ProofShape.liftN, ProofShape.subst, τ, unitParameterImages] using NZ
        | succ hl => cases hl
  have RP := static_structure_unit_lookup_compute (D := D) hi hp hx hz hS hΓ
    (show Lookup Γ 1 S from .succ .zero)
  have RQ := static_structure_unit_lookup_compute (D := D) hi hp hx hz hS hΓ
    (show Lookup Γ 0 S from .zero)
  have RI : ∀ i, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x) i) (τ i) := by
    intro i
    rw [EX]
    match i with
    | 0 => exact .app .refl RP
    | 1 => exact RQ
    | 2 => exact RP
    | i+3 => exact .refl
  have H := static_structure_subst_join_computed_native_images heq hs hΓ
    ((Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hX)
    (erasedSubstAgreement_one hΓA hX) W E HI hb RB RI
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN, EX] using H

end Lean4Lean.VEnv.Strengthening
