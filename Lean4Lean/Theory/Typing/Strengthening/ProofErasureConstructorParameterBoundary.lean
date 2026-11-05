import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedFreshTypeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePositiveHeaderRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitReturn

/-! # Retained parameters obstruct even future exact constructor recovery

A positive phantom family has one unit parameter. Its constructor at the old
unit variable also has the family type at a newly inserted unit variable.
No computation followed by native recovery can produce that exact assigned
type, although native recovery and the assignment have an explicit common
output. This distinguishes exact pivot repair from common type joining.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A saturated registered constructor with a retained parameter admits an
assignment that no future computed image can recover exactly. Both relations
may be any descending languages. Full structure eta nevertheless supplies a
common native type. This refutes eventual exact coverage, not common coverage
or strengthening. -/
theorem constructor_retained_parameter_no_exact_pivot
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) :
    ∃ Γ e A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e A ∧ ¬ IsProof Γ e ∧
      proofErase Γ e = .app (.const c []) (.bvar 1) ∧
      proofErase Γ A = .app (.const t []) (.bvar 0) ∧
      (∀ Source Target, ErasedScopedPrimitiveDescent Source → ErasedScopedPrimitiveDescent Target →
        ∀ image, ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) image →
        ¬ ScopedTypeRecovery Target (proofEraseCtx Γ) image (proofErase Γ A)) ∧
      ∀ D : PureObservation.Definitions, ∃ shared,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ e) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ A) shared := by
  let S := VExpr.const s []
  let Γ₀ := [S]
  let Γ := [S, S]
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨trivial, _, hS⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hS.weak0 henv.ordered⟩
  have hC : env.HasType univs [] (.const c [])
      (.forallE S (.app (.const t []) (.bvar 0))) := by
    have H := HasType.const (U := univs) (Γ := [])
      (henv.ordered.projectionConstructor hTag) (ls := []) (by simp) rfl
    exact H
  have hP₀ : env.HasType univs Γ₀ (.bvar 0) S := .bvar .zero
  have hP : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hQ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hE₀ : env.HasType univs Γ₀ (.app (.const c []) (.bvar 0))
      (.app (.const t []) (.bvar 0)) := .app (hC.weak0 henv.ordered) hP₀
  have hE : env.HasType univs Γ (.app (.const c []) (.bvar 1))
      (.app (.const t []) (.bvar 1)) := .app (hC.weak0 henv.ordered) hP
  have hFP : env.HasType univs Γ (.app (.const t []) (.bvar 1)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hP
  have hFQ : env.HasType univs Γ (.app (.const t []) (.bvar 0)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hQ
  have Hpq := IsDefEq.unitLike hi (params := []) hp.symm hx hz hP hQ
  have HE := IsDefEq.appDF (hF.weak0 (Γ := Γ) henv.ordered) Hpq
  have hn := not_proof_at_positive_type hΓ hFP hE
  have EP : proofErase Γ (.bvar 1) = .bvar 1 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hP)
  have EQ : proofErase Γ (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hQ)
  have EF : proofErase Γ (.const t []) = .const t [] :=
    if_neg (not_isProof_function_to_sort hΓ (hF.weak0 henv.ordered))
  have EA : proofErase Γ (.app (.const t []) (.bvar 0)) = .app (.const t []) (.bvar 0) := by
    rw [show proofErase Γ (.app (.const t []) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hFQ), EF, EQ]
  refine ⟨Γ, .app (.const c []) (.bvar 1), .app (.const t []) (.bvar 0),
    hΓ, HE.defeq hE, hn, ?_, EA, ?_, ?_⟩
  · have EC := proofErase_const_spine (c := c) (ls := []) (args := [.bvar 1]) hΓ hE hn
    simpa only [VExpr.mkApps, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, ProofShape.mkApps, EP] using
      EC
  · intro Source Target hsource htarget image RC
    rw [EA]
    exact computed_native_recovery_no_inserted_argument hsource htarget hΓ₀ hΓ
      (Ctx.LiftN.one (A := S)) hE₀ (by decide) (by decide) RC
  · intro D
    have RN := proofErase_structure_constructor_native
      (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hTag rfl
      (args := [.bvar 1]) (levels := []) rfl hE hn
    have RP := static_structure_unit_lookup_compute (D := D) hi hp hx hz hS hΓ
      (show Lookup Γ 1 S from .succ .zero)
    have RQ := static_structure_unit_lookup_compute (D := D) hi hp hx hz hS hΓ
      (show Lookup Γ 0 S from .zero)
    have RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.const c []) (.bvar 1))) (.app (.const t []) (.bvar 1)) := by
      simpa [PositiveHeaderRegistration.info, ProofShape.mkApps, EP] using RN
    exact ⟨.app (.const t []) (.const info.ctorName []), RN'.convert (.app .refl RP),
      EA ▸ ScopedCompute.app ScopedCompute.refl RQ⟩

omit [Params] in
/-- Install the positive phantom family and its constructor in an actual
well-formed projection-stage extension, retaining canonical Eq. In this
extension a literal constructor has no exactly recoverable future image,
while its native type and assigned type explicitly join in the environment
core. No arbitrary metadata or global type-joining hypothesis is assumed. -/
theorem exists_registered_constructor_without_exact_pivot
    {base : VEnv} (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hi : base.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : base.HasType 0 [] (.const s []) (.sort (.succ .zero)))
    (ht : base.constants t = none) (hc : base.constants c = none) (hne : t ≠ c) :
    ∃ E : VEnv, ∃ hE : E.WF, base ≤ E ∧ E.HasCanonicalEq ∧
      E.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c) ∧
      (letI := hE.params 0
       ∃ Γ e A, OnCtx Γ (E.IsType 0) ∧ E.HasType 0 Γ e A ∧ ¬ IsProof Γ e ∧
         proofErase Γ e = .app (.const c []) (.bvar 1) ∧
         proofErase Γ A = .app (.const t []) (.bvar 0) ∧
         (∀ image, ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
             (proofEraseCtx Γ) (proofErase Γ e) image →
           ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
             (proofEraseCtx Γ) image (proofErase Γ A)) ∧
         ∃ shared,
           ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
             (proofEraseCtx Γ) (proofErase Γ e) shared ∧
           ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
             (proofEraseCtx Γ) (proofErase Γ A) shared) := by
  let T := VExpr.forallE (.const s []) (.sort (.succ .zero))
  have HT : base.HasType 0 [] T (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  obtain ⟨envT, envC, hT, hC⟩ := PositiveHeaderRegistration.exists_constants
    (U := 0) (ps := [.const s []]) (T := T) ht hc hne
  let entry : VProjectionEntry :=
    { typeName := t, info := PositiveHeaderRegistration.info 0 [.const s []] t c }
  let E := envC.addProjections [entry]
  have hE : E.WF := PositiveHeaderRegistration.register_wf hbase hne ⟨_, HT⟩ hT hC
  have hle : base ≤ E := (VEnv.addConstVals_le hT).trans
    ((VEnv.addConstVals_le hC).trans VEnv.addProjections_le)
  have hlookup : E.constants t = some
      (PositiveHeaderRegistration.family 0 [.const s []] T t c).toVConstant :=
    ((VEnv.addConstVals_le hC).trans VEnv.addProjections_le).constants
      (VEnv.addConstVals_get hT (ci := (PositiveHeaderRegistration.family 0 [.const s []]
        T t c).toVConstVal) (by simp))
  have hTag : E.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c) :=
    VEnv.addProjections_iff.2 (.inl ⟨entry, by simp, rfl, rfl⟩)
  refine ⟨E, hE, hle, heq.mono hle, hTag, ?_⟩
  letI := hE.params 0
  have hF : E.HasType 0 [] (.const t []) T :=
    HasType.const0 hlookup ⟨_, HT.mono hle⟩
  obtain ⟨Γ, e, A, hΓ, heA, hn, Ee, EA, Hno, Hcommon⟩ :=
    constructor_retained_parameter_no_exact_pivot (hle.projections hi) hp hx hz (hS.mono hle) hTag hF
  exact ⟨Γ, e, A, hΓ, heA, hn, Ee, EA,
    Hno _ _ (erased_static_structure_eta_expansion_union_descent (heq.mono hle) EnvironmentCore.sound)
      (erased_static_structure_eta_expansion_union_descent (heq.mono hle) EnvironmentCore.sound),
    Hcommon EnvironmentCore.definitions⟩

end Lean4Lean.VEnv.Strengthening
