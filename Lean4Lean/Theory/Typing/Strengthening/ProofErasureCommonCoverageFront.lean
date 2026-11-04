import Lean4Lean.Theory.Typing.Strengthening.ProofErasureVariableCoverageJoin
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # The separate costs of common native coverage

Uniform common coverage splits into bare native existence and equality-to-join
completeness at types. The second part is already present in variable coverage
and suffices for the proposition front. Coverage also implies context transport,
so assuming coverage to prove transport would not bypass the front obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Open existence obligation: every retained typed source has some native
certificate. The selected type need not be joined to the assigned type. -/
def StaticStructureNativeExistence (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ e A}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e A → ¬ IsProof Γ e →
    ∃ native, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) native

/-- Open uniform common-coverage obligation, with proof sources exempted.
This definition does not establish native existence or equality completeness. -/
def StaticStructureCommonCoverage (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ e A}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e A → CommonNativeArgument D Γ e A

/-- Native existence plus type-conversion joins yields uniform common coverage.
Replay exposes the selected native type; uniqueness relates it to the assignment. -/
theorem StaticStructureTypeConversionJoin.common_coverage_of_existence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D) (HN : StaticStructureNativeExistence D) :
    StaticStructureCommonCoverage D := by
  intro Γ e A hΓ ht hn
  obtain ⟨native, RN⟩ := HN hΓ ht hn
  obtain ⟨B, hb, EB⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  obtain ⟨u, hA⟩ := ht.isType henv hΓ
  have HAB := (ht.uniqU henv hΓ hb).of_l henv hΓ hA
  obtain ⟨shared, RA, RB⟩ := HJ hΓ HAB
  rw [EB] at RB
  exact ⟨shared, RN.convert RB, RA⟩

/-- Uniform coverage contains two distinct demands: native existence at
arbitrary terms and common coverage at arbitrarily converted variable types.
The latter is already the full type-conversion joining problem. -/
theorem static_structure_common_coverage_iff_variable_and_existence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    StaticStructureCommonCoverage D ↔
      NativeVariableCommonCoverage D ∧ StaticStructureNativeExistence D := by
  constructor
  · intro H
    refine ⟨fun hΓ ht => H hΓ ht, ?_⟩
    intro Γ e A hΓ ht hn
    obtain ⟨native, RN, _⟩ := H hΓ ht hn
    exact ⟨native, RN⟩
  · rintro ⟨HV, HN⟩
    exact StaticStructureTypeConversionJoin.common_coverage_of_existence heq hs
      (HV.type_conversion_join heq hs) HN

/-- Uniform common coverage transports any native certificate across arbitrary
actual context equality, with a forward residual on its selected type. No domain
computation is required. This is conditional on coverage, not a transport proof
independent of equality completeness. -/
theorem StaticStructureCommonCoverage.context_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StaticStructureCommonCoverage D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HC : IsDefEqCtx env univs [] Γ Γ')
    (ht : env.HasType univs Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ native, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
        (proofErase Γ' e) native ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ') out native := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  have hn : ¬ IsProof Γ e := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have hn' : ¬ IsProof Γ' e := mt (isProof_defeqCtx HC).2 hn
  have hΓ' := (HC.symm henv.ordered).isType
  obtain ⟨native, RN', RA⟩ := H hΓ' (heA.defeqDFC henv HC) hn'
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  have EA' : proofErase Γ' A = out := (proofErase_defeqCtx hΓ HC hA).symm.trans EA
  exact ⟨native, RN', EA' ▸ RA⟩

/-- Computed-binder transport follows from uniform common coverage as a special
case of arbitrary equal-context transport. The coverage premise remains open. -/
theorem StaticStructureCommonCoverage.forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StaticStructureCommonCoverage D) : NativeForwardBinder D := by
  intro Γ A C u e T out hΓ HAC _ ht RN
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  exact H.context_transport heq hs hΓA (.succ (.refl hΓ) HAC) ht RN

/-- Type-conversion joins suffice for proposition strengthening: join the
lifted propositions, descend both computations, and reflect their common erasure.
No normalization, inhabitance assumption or strengthening theorem is used. -/
theorem StaticStructureTypeConversionJoin.propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StaticStructureTypeConversionJoin D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  obtain ⟨shared, RP, RR⟩ := H hΓ' (HE.of_l henv hΓ' hP')
  rw [proofErase_liftN hΓ hΓ' Ctx.LiftN.one hP] at RP
  rw [proofErase_liftN hΓ hΓ' Ctx.LiftN.one hR] at RR
  obtain ⟨P', HP, EP⟩ := proofErase_scoped_compute_descend
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hΓ' Ctx.LiftN.one hP rfl RP
  obtain ⟨R', HR, ER⟩ := proofErase_scoped_compute_descend
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hΓ' Ctx.LiftN.one hR rfl RR
  have EE := ProofShape.liftN_inj.mp (EP.trans ER.symm)
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ HP.hasType.2 HR.hasType.2 EE).1
    (IsDefEqU.refl ⟨_, HasType.sort (l := .zero) (by trivial)⟩)
  exact (HP.trans (((HC.defeq hΓ).of_l henv hΓ HP.hasType.2).trans HR.symm)).toU

/-- Variable-only common coverage already implies the original proposition
front. It therefore cannot be accepted as a strictly smaller sufficient gap
merely because its source syntax is restricted to one variable constructor. -/
theorem NativeVariableCommonCoverage.propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NativeVariableCommonCoverage D) : PropositionFront :=
  StaticStructureTypeConversionJoin.propositionFront heq hs (H.type_conversion_join heq hs)

end Lean4Lean.VEnv.Strengthening
