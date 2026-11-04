import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicFamilySeparation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Function eta alone still does not give common native coverage

A positive empty structure has equal inhabitants x and y. A neutral family F
can therefore assign p both F x and F y. Native recovery from the variable p
starts at F x, while full function-eta computation preserves the distinction
between the two opaque argument variables. Even common-native coverage fails.
This is an obstruction to the erased language, not to strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]
namespace AtomicControl

/-- A closed positive rigid family supplies the opaque control carrier without
any hypothesis about strengthening or the erased computation system. -/
@[instance_reducible]
def Atom.ofRigid (hr : env.Rigid c)
    (hT : env.HasType univs [] (.const c ls) (.sort (.succ u))) : Atom where
  type := .const c ls
  sortLevel := u
  closed := trivial
  typed := hT
  noPi hΓ H := IsDefEqU.rigidApp_forallE_inv henv hΓ hr
    (args := []) (hT.weak0 henv.ordered) H

end AtomicControl

/-- A family indexed by distinct variables of a positive unit-like structure
has equal actual types with no common full function-eta reduct. The declaration
collection may contain all actual quotient and selected structure equations. -/
theorem eta_unit_family_no_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort (.succ .zero))))
    (hI : env.HasType univs Γ (.bvar i) (.const family []))
    (hJ : env.HasType univs Γ (.bvar j) (.const family []))
    (hif : i ≠ f) (hjf : j ≠ f) (hij : i ≠ j) :
    env.IsDefEq univs Γ (.app (.bvar f) (.bvar i)) (.app (.bvar f) (.bvar j)) (.sort (.succ .zero)) ∧
    ¬ ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar f) (.bvar i))) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar f) (.bvar j))) shared := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have HE : env.IsDefEq univs Γ (.bvar i) (.bvar j) (.const family []) :=
    IsDefEq.unitLike hi (params := []) hp.symm hx hz hI hJ
  have HA : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort (.succ .zero)) := .app hF hI
  have HB : env.HasType univs Γ (.app (.bvar f) (.bvar j)) (.sort (.succ .zero)) := .app hF hJ
  have EF : proofErase Γ (.bvar f) = .bvar f :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom (.sort (.succ .zero))) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .atom) hΓ hI)
  have EJ : proofErase Γ (.bvar j) = .bvar j :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .atom) hΓ hJ)
  have EA : proofErase Γ (.app (.bvar f) (.bvar i)) = .app (.bvar f) (.bvar i) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from if_neg (not_isProof_of_sort hΓ HA), EF, EI]
  have EB : proofErase Γ (.app (.bvar f) (.bvar j)) = .app (.bvar f) (.bvar j) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar j)) = .app _ _ from if_neg (not_isProof_of_sort hΓ HB), EF, EJ]
  refine ⟨IsDefEq.appDF hF HE, ?_⟩
  rw [EA, EB]
  exact AtomicControl.eta_union_family_arguments_no_join heq hs
    ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, hI, EI⟩ ⟨Γ, _, hΓ, rfl, hJ, EJ⟩
    ⟨Γ, _, hΓ, rfl, HA, EA⟩ ⟨Γ, _, hΓ, rfl, HB, EB⟩ hif hjf hij

/-- If p is declared at F x, its convertible assignment F y has no common
native reduct in the full function-eta union. Both type branches may use all
singleton stages and every controlled beta/eta expansion. -/
theorem eta_unit_common_native_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort (.succ .zero))))
    (hI : env.HasType univs Γ (.bvar i) (.const family []))
    (hJ : env.HasType univs Γ (.bvar j) (.const family []))
    (hif : i ≠ f) (hjf : j ≠ f) (hij : i ≠ j)
    (hl : Lookup Γ p (.app (.bvar f) (.bvar i))) :
    env.HasType univs Γ (.bvar p) (.app (.bvar f) (.bvar j)) ∧ ¬ IsProof Γ (.bvar p) ∧
    ∀ native shared, ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.bvar p)) native →
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar f) (.bvar j))) shared →
      ¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) native shared := by
  obtain ⟨HE, Hno⟩ := eta_unit_family_no_join heq hs hi hp hx hz hS hΓ hF hI hJ hif hjf hij
  have hP : env.HasType univs Γ (.bvar p) (.app (.bvar f) (.bvar i)) := .bvar hl
  have hn := not_proof_at_positive_type hΓ HE.hasType.1 hP
  refine ⟨HE.defeq hP, hn, ?_⟩
  intro native shared RN RA RT
  rw [show proofErase Γ (.bvar p) = .bvar p from if_neg hn] at RN
  have RC := RN.bvar_compute
  rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl] at RC
  exact Hno ⟨shared, RC.trans RT, RA⟩

/-- A registered closed positive empty structure supplies the complete
four-variable context. No hypothesized family or source typing remains; the
family is an ordinary context variable and its two indices are unit inhabitants. -/
theorem eta_unit_common_native_failure_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      ∀ native shared, ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) native shared := by
  let S := VExpr.const family []
  let FT := VExpr.forallE S (.sort (.succ .zero))
  let Γ₀ := [FT, S, S]
  have hFT : env.HasType univs [] FT (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩, _, hFT.weak0 henv.ordered⟩
  have hF₀ : env.HasType univs Γ₀ (.bvar 0) FT := .bvar .zero
  have hI₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hA : env.HasType univs Γ₀ (.app (.bvar 0) (.bvar 1)) (.sort (.succ .zero)) := .app hF₀ hI₀
  let Γ := .app (.bvar 0) (.bvar 1) :: Γ₀
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hA⟩
  have hF : env.HasType univs Γ (.bvar 1) FT := .bvar (.succ .zero)
  have hI : env.HasType univs Γ (.bvar 2) S := .bvar (.succ (.succ .zero))
  have hJ : env.HasType univs Γ (.bvar 3) S := .bvar (.succ (.succ (.succ .zero)))
  have hl : Lookup Γ 0 (.app (.bvar 1) (.bvar 2)) := .zero
  exact ⟨Γ, .bvar 0, .app (.bvar 1) (.bvar 3), hΓ,
    eta_unit_common_native_failure heq hs hi hp hx hz hS hΓ hF hI hJ
      (by decide) (by decide) (by decide) hl⟩

/-- The actual augmented environment core does not repair this omission:
quotient-prefix and selected structure equations are all present, but structure
eta on opaque inhabitants is absent from the computation grammar. -/
theorem environment_eta_unit_common_native_failure
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      ∀ native shared, ScopedTypeRecovery (ErasedEtaExpansionUnion EnvironmentCore.definitions)
          (proofEraseCtx Γ) (proofErase Γ p) native →
        ScopedCompute (ErasedEtaExpansionUnion EnvironmentCore.definitions)
          (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedEtaExpansionUnion EnvironmentCore.definitions)
          (proofEraseCtx Γ) native shared :=
  eta_unit_common_native_failure_context heq EnvironmentCore.sound hi hp hx hz hS

end Lean4Lean.VEnv.Strengthening
