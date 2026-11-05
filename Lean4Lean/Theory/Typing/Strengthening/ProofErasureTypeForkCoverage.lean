import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeForkFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeJoinNativeExistence

/-! # Exact scope of the remaining type-fork premise

In the concrete presentation, type-fork joining is equivalent to ordinary
type-conversion joining and to uniform common native coverage. The forward
implications use declaration-history completeness; the reverse implication
reifies the two computed endpoints. These equivalences identify the remaining
obligation without asserting that it is strictly smaller than PropositionFront.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Equality-to-join completeness joins forks by realizing both outputs as
ordinary equal types. No completeness for arbitrary data values is needed. -/
theorem StaticStructureTypeConversionJoin.type_forks
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D) : TypeForkJoin D := by
  intro Γ T u left right hΓ hT RL RR
  obtain ⟨A, HA, EA⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RL
  obtain ⟨B, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RR
  obtain ⟨shared, RA, RB⟩ := HJ hΓ (HA.symm.trans HB)
  exact ⟨shared, EA ▸ RA, EB ▸ RB⟩

/-- For the actual environment core, type-fork joining and ordinary type
conversion joining are equivalent open obligations. Restricting the premise
to forks does not remove the equality-completeness cost in this presentation. -/
theorem environment_core_type_forks_iff_conversion_join
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r) :
    TypeForkJoin EnvironmentCore.definitions ↔
      StaticStructureTypeConversionJoin EnvironmentCore.definitions :=
  ⟨fun HF => type_conversion_join_of_type_forks heq HF hregistry hcon hqpat hguard,
    fun HJ => HJ.type_forks heq EnvironmentCore.sound⟩

/-- Type-fork joining supplies all common native certificates, including at
arbitrarily converted variable assignments. Native existence is derived from
readout and source syntax; it is not a second premise. Fork joining remains open. -/
theorem common_native_coverage_of_type_forks
    (heq : env.HasCanonicalEq) (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r) :
    StaticStructureCommonCoverage EnvironmentCore.definitions :=
  StaticStructureTypeConversionJoin.common_coverage heq EnvironmentCore.sound
    (type_conversion_join_of_type_forks heq HF hregistry hcon hqpat hguard)
    (fun hi => EnvironmentCore.no_rigid (henv.projectionRigid hi))

/-- Uniform common coverage contains exactly the type-fork obligation in the
concrete presentation. Therefore it cannot be used as independent evidence for
fork joining without discharging the same remaining gap. -/
theorem environment_core_type_forks_iff_common_coverage
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r) :
    TypeForkJoin EnvironmentCore.definitions ↔
      StaticStructureCommonCoverage EnvironmentCore.definitions := by
  constructor
  · exact fun HF => common_native_coverage_of_type_forks heq HF hregistry hcon hqpat hguard
  · intro HC
    have HV : NativeVariableCommonCoverage EnvironmentCore.definitions := by
      intro Γ i A hΓ ht
      exact HC hΓ ht
    intro Γ T u left right hΓ hT RL RR
    exact StaticStructureTypeConversionJoin.type_forks heq EnvironmentCore.sound
      (HV.type_conversion_join heq EnvironmentCore.sound) hΓ hT RL RR

end Lean4Lean.VEnv.Strengthening
