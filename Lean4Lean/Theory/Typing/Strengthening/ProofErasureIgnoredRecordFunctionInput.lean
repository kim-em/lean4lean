import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordInput

/-! # Unknown functions returning dependent record instances

The actual oracle ends in a literal family application, whose parameter may
depend on the argument. That argument needs only ordinary typing: it has no
observation demand, native certificate, or prescribed computational history.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- The unknown function consumes no argument observations and returns a
record value. Its actual dependent oracle type is checked separately. -/
def RecordFunctionInput (i : Nat) (domain : HeterogeneousControl.ControlType) : Sets :=
  fun j key => j = i ∧ key = .fn domain [] .record

/-- Lookup at a literal family-ending Pi initializes the joint observer.
Ordinary uniqueness of its dependent parameter converts only the value's
control typing; the native oracle retains its actual dependent family body. -/
theorem record_function_input_observation (domain : HeterogeneousControl.ControlType)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.app (.const t []) p)))
    (hx : env.HasType univs Γ x domain.expr) :
    (RecordFunctionInput f domain).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (RecordFunctionInput f domain) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (RecordFunctionInput f domain)
        (.app (.bvar f) (proofErase Γ x)) .record := by
  have hA : env.HasType univs Γ domain.expr (.sort domain.level) :=
    HeterogeneousControl.ControlType.typed (HeterogeneousControl.ControlTyping.of_typed hΓ hx).wf
  have hΓA : OnCtx (domain.expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf₀ : env.HasType univs Γ (.bvar f) (.forallE domain.expr (.app (.const t []) p)) := .bvar hl
  obtain ⟨_, hPi₀⟩ := hf₀.isType henv hΓ
  obtain ⟨_, _, hBody⟩ := hPi₀.forallE_inv henv.ordered
  have hp := family_parameter hi hS Q hF hΓA hBody
  have hFamily := hF.weak0 (Γ := domain.expr :: Γ) henv.ordered
  have hB := hFamily.app hp
  have HE := IsDefEq.appDF hFamily (Q.value_equal hi hS hp)
  have hf : env.HasType univs Γ (.bvar f)
      (HeterogeneousControl.ControlType.arrow domain (.atom RT)).expr :=
    (IsDefEq.forallEDF hA HE).defeq hf₀
  have EF : proofErase Γ (.bvar f) = .bvar f :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have HF : HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar f) (.arrow domain (.atom RT)) :=
    ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have hPi := HasType.forallE hA hB
  have EP : proofErase Γ (.forallE domain.expr (.app (.const t []) p)) =
      .forallE (proofErase Γ domain.expr) (proofErase (domain.expr :: Γ) (.app (.const t []) p)) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HO : Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (RecordFunctionInput f domain)
      (proofErase Γ (.forallE domain.expr (.app (.const t []) p))) (.type (.fn domain [] .record)) := by
    rw [EP]
    exact .pi ⟨Γ, _, hΓ, rfl, hPi, EP⟩ ⟨Γ, _, hΓ, rfl, hA, rfl⟩ (by simp) (by simp)
      (family_observation hi hS Q hTag hF hΓA hp)
  have he : env.HasType univs Γ (.app (.bvar f) x) (HeterogeneousControl.ControlType.atom RT).expr := by
    simpa only [HasType, VExpr.inst_eq, VExpr.Subst.liftN, HeterogeneousControl.ControlType.expr_subst] using hf.app hx
  have EE : proofErase Γ (.app (.bvar f) x) = .app (.bvar f) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.bvar f) x) = .app _ _ from
      if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EF]
  refine ⟨?_, ?_, .app ⟨Γ, _, hΓ, rfl, he, EE⟩ (.var HF (by simp [Key.Valid]) ⟨rfl, rfl⟩) (by simp)⟩
  · rintro j key ⟨rfl, rfl⟩; exact HF
  · rintro j key ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact E ▸ HO

include hi hS Q hTag hF

/-- Full computation of an unknown function application and all subsequent
native-type computation expose the family head after every raw substitution.
The caller argument has ordinary typing only. -/
theorem record_function_native_head_readout (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.app (.const t []) p)))
    (hx : env.HasType univs Γ x domain.expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ∃ a, BetaRed (out.subst σ) (.app (.const t []) a) := by
  obtain ⟨HS, HV, H⟩ := record_function_input_observation hi hS Q hTag hF domain hΓ hl hx
  exact program_native_head_readout hi hS Q hTag hF heq hs huc hc hf H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) RE RN RA

/-- A certified target telescope completes the substituted native history of
the unknown function application, independently of the source oracle's domain. -/
theorem record_function_native_telescope_return (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.app (.const t []) p)))
    (hx : env.HasType univs Γ x domain.expr)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) Δ' (.const t []) T')
    (HC : CallerCanonicalTelescope Target Δ' T' 1 cs)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) Δ'
      (out.subst σ) (ProofShape.mkApps (.const t []) cs) := by
  obtain ⟨a, RB⟩ := record_function_native_head_readout hi hS Q hTag hF domain (σ := σ)
    heq hs huc hc hf hΓ hl hx RE RN RA
  exact (ScopedCompute.beta RB).trans (HC.compute (args := [a]) RF rfl)

/-- An unknown function applied to an arbitrary typed argument has the same
native/assigned join as a concrete constructor. Its actual oracle is a literal
dependent family-ending Pi; all source observation and target recovery premises
are discharged, and the final raw substitution remains unrestricted. -/
theorem record_function_environment_native_assigned_join (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.app (.const t []) p)))
    (hx : env.HasType univs Γ x domain.expr)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := record_function_input_observation hi hS Q hTag hF domain hΓ hl hx
  exact program_environment_native_assigned_join hi hS Q hTag hF heq hcf hU hT H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
