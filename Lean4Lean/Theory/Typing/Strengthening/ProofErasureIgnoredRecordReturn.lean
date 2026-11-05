import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordReadout

/-! # Full constructor/native return for arbitrary higher-order parameters

The supplied parameter is any ordinary typed term at a finite unit-arrow type.
All subsequent term computation, native selection, and type computation are
unrestricted. Beta head readout then survives arbitrary raw substitution; the
target caller installs its canonical argument without inspecting that image.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets unitCarrier UnitArrows)
variable [Params] {D Target : PureObservation.Definitions}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- Any ordinarily typed parameter initializes the empty-demand constructor
observer. It need not have a native certificate or belong to an observation
fragment. Its own computation paths can be arbitrary. -/
theorem initial_observation
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr) :
    Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (fun _ _ => False)
      (.app (.const c []) (proofErase Γ x)) .record := by
  have hf : env.HasType univs Γ (.const c [])
      (HeterogeneousControl.ControlType.arrow (Q.control U) (.atom RT)).expr :=
    (constructor_simple_arrow hi hS Q hTag hF).weak0 henv.ordered
  have ht : env.HasType univs Γ (.app (.const c []) x) (HeterogeneousControl.ControlType.atom RT).expr := by
    simpa only [HasType, VExpr.inst_eq, VExpr.Subst.liftN, HeterogeneousControl.ControlType.expr_subst] using hf.app hx
  have EF : proofErase Γ (.const c []) = .const c [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have EE : proofErase Γ (.app (.const c []) x) = .app (.const c []) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.const c []) x) = .app _ _ from
      if_neg (HeterogeneousControl.ControlType.not_isProof hΓ ht), EF]
  exact .app ⟨Γ, _, hΓ, rfl, ht, EE⟩ (.record_ctor ⟨Γ, _, hΓ, rfl, hf, EF⟩) (by simp)

include hi hS Q hTag hF

/-- Every full constructor continuation beta-exposes its original head, under
any raw substitution. No parameter history or readout premise remains. -/
theorem constructor_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) out) :
    ∃ a, BetaRed (out.subst σ) (.app (.const c []) a) := by
  have H := initial_observation hi hS Q hTag hF hΓ hx
  exact (H.full_compute hi hS Q hTag hF heq hs huc hc hf
    (by intro i key h; cases h) (by intro i key h; cases h) RE).constructor_head

/-- Every native selection after arbitrary constructor computation, and every
later type computation, beta-exposes the registered family. Raw substitution
of the final type is arbitrary, so its image needs no native recovery. -/
theorem native_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ∃ a, BetaRed (out.subst σ) (.app (.const t []) a) := by
  have H := initial_observation hi hS Q hTag hF hΓ hx
  have HS : Sets.Typed U RT (proofEraseCtx Γ) (fun _ _ => False) := by intro i key h; cases h
  have HV : Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (fun _ _ => False) := by intro i key h; cases h
  have HE := H.full_compute hi hS Q hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS Q hTag hF heq hs huc hc hf HS HV RN
  exact (HN.full_compute hi hS Q hTag hF heq hs huc hc hf HS HV RA).family_head

/-- Any actual target canonical telescope completes the substituted native
history. Its selected annotations may differ from the source parameter type;
all target computation evidence is contained in the telescope certificate. -/
theorem native_substitution_telescope_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) Δ' (.const t []) T')
    (HC : CallerCanonicalTelescope Target Δ' T' 1 cs)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) Δ'
      (out.subst σ) (ProofShape.mkApps (.const t []) cs) := by
  obtain ⟨a, RB⟩ := native_head_readout hi hS Q hTag hF (σ := σ) heq hs huc hc hf hΓ hx RE RN RA
  exact (ScopedCompute.beta RB).trans (HC.compute (args := [a]) RF rfl)

/-- A target family native header completes arbitrary substituted native-type
histories. Source and target contexts and definition collections may differ;
no interpretation or typing of the raw substitution is requested. -/
theorem native_substitution_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (ht : Target.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ')
      (.const t []) (.forallE (Q.raw s) B))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ')
      (out.subst σ) (.app (.const t []) (Q.canonical s uc)) := by
  exact native_substitution_telescope_return hi hS Q hTag hF (cs := [Q.canonical s uc])
    heq hs huc hc hf hΓ hx RF (Q.caller_telescope hi hS heq ht hΓ' .nil) RE RN RA

/-- Actual stored family data discharges the target native premise for full
constructor/native histories with arbitrary supplied finite-order functions.
The resulting type computation survives every raw substitution into any actual
well-formed target context. No global native coverage is assumed. -/
theorem environment_stored_native_substitution_return
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (out.subst σ) (.app (.const t []) (Q.canonical s uc)) :=
  native_substitution_return hi hS Q hTag hF heq EnvironmentCore.sound EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hx hΓ'
    (Q.stored_family_native hi hS hΓ' hcf hU hT) RE RN RA

/-- Every substituted native type of an arbitrary computed constructor joins
an independently computed assigned family in the target context. All source
parameters are ordinarily typed, all histories are full-union, and every native
or telescope premise is discharged from actual stored declaration data. -/
theorem environment_stored_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (Q.control U).expr)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const c []) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) :=
  ⟨environment_stored_native_substitution_return hi hS Q hTag hF heq hcf hU hT hΓ hx hΓ' RE RN RA,
    Q.environment_stored_family_return hi hS heq hTag rfl hcf hU hT hΓ' hAssigned RB⟩

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
