import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonCoverageFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Native existence from type-conversion joining

Joining ordinary equal types suffices for native recovery of every retained
term, provided registered family names have no selected delta rules. The proof
uses sort, Pi and rigid-family readout, followed by induction on source syntax.
Type-conversion joining remains an explicit open premise throughout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Joining the assigned type with a replayed native type upgrades any existing
native certificate to common coverage. This uses the explicit joining premise. -/
theorem StaticStructureTypeConversionJoin.common_of_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ shared, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) shared := by
  obtain ⟨B, hb, EB⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  obtain ⟨u, hA⟩ := ht.isType henv hΓ
  obtain ⟨shared, RA, RB⟩ := HJ hΓ ((ht.uniqU henv hΓ hb).of_l henv hΓ hA)
  exact ⟨shared, RN.convert (EB ▸ RB), RA⟩

/-- Type-conversion joining and sort readout expose a native universe from any
existing certificate for a sort-typed expression. -/
theorem StaticStructureTypeConversionJoin.recover_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ v, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.sort v) := by
  obtain ⟨shared, RN, RC⟩ := HJ.common_of_native heq hs hΓ ht RN
  obtain ⟨_, hU⟩ := ht.isType henv hΓ
  rw [show proofErase Γ (.sort u) = .sort u from if_neg (not_isProof_of_sort hΓ hU)] at RC
  obtain ⟨v, _, _, RN⟩ := static_structure_native_sort_of_common heq hs hΓ ht RN RC
  exact ⟨v, RN⟩

/-- Pi-origin readout supplies the literal Pi required by native application;
the chosen domain and codomain need not match the assigned syntax. -/
theorem StaticStructureTypeConversionJoin.recover_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.forallE X Y) := by
  obtain ⟨shared, RN, RC⟩ := HJ.common_of_native heq hs hΓ ht RN
  obtain ⟨_, hPi⟩ := ht.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RC
  obtain ⟨X, Y, _, RB⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RC
  exact ⟨X, Y, RN.convert (.beta RB)⟩

/-- Rigid family readout exposes an actual registered family assignment for a
native major. Both arguments and universe instances may change. -/
theorem StaticStructureTypeConversionJoin.recover_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ ls' args', env.HasType univs Γ e (VExpr.mkApps (.const s ls') args') ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) (proofErase Γ (VExpr.mkApps (.const s ls') args')) := by
  obtain ⟨shared, RN, RC⟩ := HJ.common_of_native heq hs hΓ ht RN
  obtain ⟨_, hF⟩ := ht.isType henv hΓ
  obtain ⟨ls', rawArgs, _, RB⟩ :=
    RigidDemandProfile.static_structure_registered_family_head_readout heq hs hi hD hΓ hF RC
  have RN' := RN.convert (.beta RB)
  obtain ⟨F, heF, EF⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN'
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EF
  exact ⟨ls', args', heF, EF ▸ RN'⟩

/-- Type-conversion joining supplies native existence by syntax induction.
The only restriction on selected delta equations is that registered projection
families do not unfold. No separate native-existence premise is used. -/
theorem StaticStructureTypeConversionJoin.native_existence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hD : ∀ {s info}, env.projections s info → ∀ levels rhs, ¬ D.unfolds s levels rhs) :
    StaticStructureNativeExistence D := by
  intro Γ e T hΓ ht hn
  induction e generalizing Γ T with
  | bvar i =>
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
    exact ⟨_, .bvar⟩
  | sort u =>
    rw [show proofErase Γ (.sort u) = .sort u from if_neg hn]
    exact ⟨_, .sort (HasType.sort_inv henv.ordered ht)⟩
  | const c ls =>
    obtain ⟨ci, hc, hw, hl⟩ := HasType.const_inv henv hΓ ht
    rw [show proofErase Γ (.const c ls) = .const c ls from if_neg hn]
    exact ⟨_, .const hc hw hl⟩
  | lam A b _ ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨B, R⟩ := ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (fun hp => hn (hp.lam hΓ hA))
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact ⟨_, .lam R⟩
  | app f a ihf _ =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨_, R⟩ := ihf hΓ hf (not_isProof_fn hΓ hf ha hn)
    obtain ⟨D, C, R⟩ := HJ.recover_pi heq hs hΓ hf R
    rw [show proofErase Γ (.app f a) = .app _ _ from if_neg hn]
    exact ⟨_, .app R⟩
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨_, RA⟩ := ihA hΓ hA (not_isProof_of_sort hΓ hA)
    obtain ⟨_, RB⟩ := ihB hΓA hB (not_isProof_of_sort hΓA hB)
    obtain ⟨u', RA⟩ := HJ.recover_sort heq hs hΓ hA RA
    obtain ⟨v', RB⟩ := HJ.recover_sort heq hs hΓA hB RB
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg hn]
    exact ⟨_, .forallE RA RB⟩
  | proj s j m ihm =>
    obtain ⟨info, ls, ps, idx, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, R⟩ := ihm hΓ hm.hasType.2 (not_isProof_major hΓ ht hn)
    obtain ⟨ls', args', hmF, RF⟩ := HJ.recover_family heq hs hi (hD hi) hΓ hm.hasType.2 R
    obtain ⟨u, hF⟩ := hmF.isType henv hΓ
    obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const s ls') args') from
      ⟨_, hF⟩).of_mkApps henv hΓ
    obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ hhead
    obtain ⟨doms, result, HT⟩ := projection_telescope_exists hi hw
    obtain ⟨hj, F, hpj, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT ht hn hmF
    rw [proofErase_const_spine hΓ hF (not_isProof_of_sort hΓ hF)] at RF
    have hlen := StructureReplay.family_arity henv hΓ hi ⟨u, hF⟩
    refine ⟨projectionType s info doms j hj (args'.map (proofErase Γ)) (proofErase Γ m), ?_⟩
    rw [show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg hn]
    exact ScopedTypeRecovery.proj hi HT hj (by simpa only [List.length_map] using hlen) RF

/-- Under rigid-family non-unfolding, type-conversion joining supplies common
coverage for every retained source. Native existence is derived, not assumed. -/
theorem StaticStructureTypeConversionJoin.common_coverage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : StaticStructureTypeConversionJoin D)
    (hD : ∀ {s info}, env.projections s info → ∀ levels rhs, ¬ D.unfolds s levels rhs) :
    StaticStructureCommonCoverage D :=
  StaticStructureTypeConversionJoin.common_coverage_of_existence heq hs HJ
    (HJ.native_existence heq hs hD)

/-- Variable coverage already carries the entire uniform coverage obligation,
provided selected delta rules leave registered family heads fixed. This is an
equivalence of open obligations, not a proof of proposition strengthening. -/
theorem native_variable_coverage_iff_uniform
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {s info}, env.projections s info → ∀ levels rhs, ¬ D.unfolds s levels rhs) :
    NativeVariableCommonCoverage D ↔ StaticStructureCommonCoverage D := by
  constructor
  · intro HV
    exact StaticStructureTypeConversionJoin.common_coverage heq hs
      (HV.type_conversion_join heq hs) hD
  · intro HC Γ i A hΓ ht
    exact HC hΓ ht

/-- In the actual environment core, rigid-family non-unfolding is automatic.
Thus arbitrary converted variable assignments are the whole common-coverage
problem for this fixed computation language. Both sides remain open. -/
theorem environment_core_variable_coverage_iff_uniform
    (heq : env.HasCanonicalEq) :
    NativeVariableCommonCoverage EnvironmentCore.definitions ↔
      StaticStructureCommonCoverage EnvironmentCore.definitions :=
  native_variable_coverage_iff_uniform heq EnvironmentCore.sound
    (fun hi => EnvironmentCore.no_rigid (henv.projectionRigid hi))

end Lean4Lean.VEnv.Strengthening
