import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordTypeReadout

/-! # Unknown record inputs with actual family annotations

The source value may be an unknown context variable. Its actual lookup type,
rather than a constructor ancestry certificate, supplies the family observation.
The parameter can be any ordinarily typed finite unit-arrow value.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets unitCarrier UnitArrows)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

include hF in
/-- Ordinary typing of a literal family application recovers its parameter at
the registered domain. No computational exposure or native recovery is used. -/
theorem family_parameter (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (.app (.const t []) p) (.sort u)) :
    env.HasType univs Γ p (Q.control U).expr := by
  obtain ⟨_, _, hf, hp⟩ := hT.app_inv henv hΓ
  exact argument_at_displayed_domain hΓ hf (hF.weak0 henv.ordered) hp

/-- Ordinary singleton equality presents any assigned family instance at the
fixed record control carrier. This is not a directed type computation. -/
theorem family_value_control (hp : env.HasType univs Γ p (Q.control U).expr)
    (hx : env.HasType univs Γ x (.app (.const t []) p)) :
    env.HasType univs Γ x (HeterogeneousControl.ControlType.atom RT).expr := by
  exact (IsDefEq.appDF (hF.weak0 henv.ordered) (Q.value_equal hi hS hp)).defeq hx

include hF in
/-- A literal family application retains its raw head during proof erasure. -/
theorem family_erasure (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr) :
    proofErase Γ (.app (.const t []) p) = .app (.const t []) (proofErase Γ p) := by
  have hf := hF.weak0 (Γ := Γ) henv.ordered
  rw [show proofErase Γ (.app (.const t []) p) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ (hf.app hp)),
    show proofErase Γ (.const t []) = .const t [] from
      if_neg (not_isProof_function_to_sort hΓ hf)]

/-- Every literal typed family application is observed independently of its
parameter and ambient demand set. The family head is operational evidence. -/
theorem family_observation (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr) :
    Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S
      (proofErase Γ (.app (.const t []) p)) (.type .record) := by
  have hf : env.HasType univs Γ (.const t [])
      (HeterogeneousControl.ControlType.arrow (Q.control U)
        (.sort (HeterogeneousControl.ControlType.atom RT).level)).expr := hF.weak0 henv.ordered
  have EF : proofErase Γ (.const t []) = .const t [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  rw [family_erasure hi hS Q hF hΓ hp]
  exact .app ⟨Γ, _, hΓ, rfl, hf.app hp, family_erasure hi hS Q hF hΓ hp⟩
    (.family ⟨Γ, _, hΓ, rfl, hf, EF⟩) (by simp)

/-- A single unknown record value supplies no family-type head itself. -/
def RecordInput (i : Nat) : Sets := fun j key => j = i ∧ key = .record

/-- Actual lookup discharges both the value typing and native oracle demand
for an unknown record. Its parameter typing is derived from that lookup. -/
theorem record_input_observation (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.app (.const t []) p)) :
    (RecordInput i).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (RecordInput i) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (RecordInput i) (.bvar i) .record := by
  have hx : env.HasType univs Γ (.bvar i) (.app (.const t []) p) := .bvar hl
  obtain ⟨_, hT⟩ := hx.isType henv hΓ
  have hp := family_parameter hi hS Q hF hΓ hT
  have hxc := family_value_control hi hS Q hTag hF hp hx
  have EX : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hxc)
  have HX : HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.atom RT) :=
    ⟨Γ, _, hΓ, rfl, hxc, EX⟩
  refine ⟨?_, ?_, .var HX (by simp [Key.Valid]) ⟨rfl, rfl⟩⟩
  · rintro j key ⟨rfl, rfl⟩; exact HX
  · rintro j key ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact E ▸ family_observation hi hS Q hTag hF hΓ hp

include hi hS Q hTag hF

/-- Every native type selected after arbitrary computation of an unknown
record exposes the family head, even after arbitrary raw substitution. The
value itself need not expose a constructor or admit any terminating history. -/
theorem record_input_native_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.app (.const t []) p))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ∃ a, BetaRed (out.subst σ) (.app (.const t []) a) := by
  obtain ⟨HS, HV, H⟩ := record_input_observation hi hS Q hTag hF hΓ hl
  exact program_native_head_readout hi hS Q hTag hF heq hs huc hc hf H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) RE RN RA

/-- A target canonical telescope completes the entire unknown-record native
history after raw substitution. Its target context and definitions are arbitrary. -/
theorem record_input_native_telescope_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.app (.const t []) p))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) Δ' (.const t []) T')
    (HC : CallerCanonicalTelescope Target Δ' T' 1 cs)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) Δ'
      (out.subst σ) (ProofShape.mkApps (.const t []) cs) := by
  obtain ⟨a, RB⟩ := record_input_native_head_readout hi hS Q hTag hF (σ := σ)
    heq hs huc hc hf hΓ hl RE RN RA
  exact (ScopedCompute.beta RB).trans (HC.compute (args := [a]) RF rfl)

/-- The unknown-record case of the native/assigned join has no observation,
native-coverage, or target-telescope premise. Literal source lookup and actual
stored target declaration data discharge those requirements. -/
theorem record_input_environment_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.app (.const t []) p))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := record_input_observation hi hS Q hTag hF hΓ hl
  exact program_environment_native_assigned_join hi hS Q hTag hF heq hcf hU hT H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
