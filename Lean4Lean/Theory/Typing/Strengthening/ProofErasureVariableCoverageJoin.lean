import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Variable coverage already asks for type-conversion joins

Common native coverage at an arbitrarily converted variable assignment is not a
routine lookup lemma. A generic function-to-sort variable tests arbitrary type
conversion, including conversion between propositions. Pi-origin extraction
turns its common native certificate into a join of the original domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Open coverage obligation restricted to variables. The assigned type may
be any convertible type, not just the literal lookup type. No coverage proof is
provided by this definition. -/
def NativeVariableCommonCoverage (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ i A}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ (.bvar i) A →
    CommonNativeArgument D Γ (.bvar i) A

/-- Open equality-completeness obligation for typed types in the full enriched
computation language. Unlike fork confluence, the premise is arbitrary ordinary
definitional equality and supplies no common computational predecessor. -/
def StaticStructureTypeConversionJoin (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A B u}, OnCtx Γ (env.IsType univs) → env.IsDefEq univs Γ A B (.sort u) →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) shared

/-- For a retained generic variable, common coverage joins its declared and
assigned types. Certificate descent removes the generic binder from both paths. -/
theorem NativeVariableCommonCoverage.retained_type_conversion_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NativeVariableCommonCoverage D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hn : ¬ IsProof (A :: Γ) (.bvar 0)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hx : env.HasType univs (A :: Γ) (.bvar 0) B.lift :=
    (HAB.weakN henv Ctx.LiftN.one).defeq (show env.HasType univs (A :: Γ) (.bvar 0) A.lift from .bvar .zero)
  obtain ⟨shared, RN, RB⟩ := H hΓA hx hn
  rw [show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at RN
  have RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      ((proofErase Γ A).liftN 1) shared := RN.bvar_compute
  rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one HAB.hasType.2] at RB
  obtain ⟨A', _, RA', EA⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one HAB.hasType.1 rfl RA
  obtain ⟨B', _, RB', EB⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one HAB.hasType.2 rfl RB
  have E := ProofShape.liftN_inj.mp (EA.trans EB.symm)
  exact ⟨proofErase Γ A', RA', E ▸ RB'⟩

/-- Variable coverage joins every pair of equal types, including propositions.
A function-to-sort probe retains its generic variable; Pi component histories
then remove the probe without any native certificate for either domain. -/
theorem NativeVariableCommonCoverage.type_conversion_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NativeVariableCommonCoverage D) : StaticStructureTypeConversionJoin D := by
  intro Γ A B u hΓ HAB
  have hA := HAB.hasType.1
  have hB := HAB.hasType.2
  have HP := IsDefEq.forallEDF HAB (HasType.sort (l := .zero) (by trivial))
  have hΓF : OnCtx (.forallE A (.sort .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, HP.hasType.1⟩
  have hn : ¬ IsProof (.forallE A (.sort .zero) :: Γ) (.bvar 0) :=
    not_isProof_function_to_sort hΓF (show env.HasType univs
      (.forallE A (.sort .zero) :: Γ) (.bvar 0) (.forallE A.lift (.sort .zero)) from .bvar .zero)
  obtain ⟨shared, RA, RB⟩ := H.retained_type_conversion_join heq hs hΓ HP hn
  have E (X : VExpr) (hX : env.HasType univs Γ X (.sort u)) :
      proofErase Γ (.forallE X (.sort .zero)) =
        .forallE (proofErase Γ X) (proofErase (X :: Γ) (.sort .zero)) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hX (HasType.sort (by trivial))))
  rw [E A hA] at RA
  rw [E B hB] at RB
  obtain ⟨X, Y, HO, Rbeta⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ hA
    (HasType.sort (by trivial)) RA
  have HB := proofErase_static_structure_union_pi_components heq hs hΓ hB
    (HasType.sort (by trivial)) (RB.trans (.beta Rbeta))
  obtain ⟨_, _, _, _, _, _, RAX, _⟩ := HO
  obtain ⟨_, _, _, _, _, _, RBX, _⟩ := HB
  exact ⟨X, RAX, RBX⟩

/-- Conversely, equality-to-join completeness supplies common native variable
coverage by joining the literal lookup type to the assigned type. -/
theorem StaticStructureTypeConversionJoin.variable_common_coverage
    (H : StaticStructureTypeConversionJoin D) : NativeVariableCommonCoverage D := by
  intro Γ i A hΓ ht hn
  obtain ⟨B, HL⟩ := ht.bvar_inv henv hΓ
  have hb : env.HasType univs Γ (.bvar i) B := .bvar HL
  obtain ⟨u, hB⟩ := hb.isType henv hΓ
  have HBA := (hb.uniqU henv hΓ ht).of_l henv hΓ hB
  obtain ⟨shared, RB, RA⟩ := H hΓ HBA
  exact ⟨shared, proofErase_scoped_lookup_recovery hΓ HL hn RB, RA⟩

/-- Even variable-only common coverage is exactly equality-to-join completeness
for types. This is not a proof of either open obligation or a strict reduction
of proposition strengthening. -/
theorem native_variable_coverage_iff_type_conversion_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    NativeVariableCommonCoverage D ↔ StaticStructureTypeConversionJoin D :=
  ⟨fun H => H.type_conversion_join heq hs, fun H => H.variable_common_coverage⟩

end Lean4Lean.VEnv.Strengthening
