import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRegisteredCanonicalTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitArrowCanonical
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Full family return for arbitrary retained unit-arrow arguments

A literal native unit-arrow domain supplies the canonical telescope. Rigid head
readout handles arbitrary whole-family computation, with no observation or native
certificate for its argument. The substitution result also repairs computations
started before a binder is instantiated.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {D Target : PureObservation.Definitions}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
local notation "U" => unitCarrier hi hS
include hi hS

/-- Every finite simple unit profile extends a canonical caller telescope.
The remaining raw codomain may be dependent and need not expose a sort. -/
theorem UnitArrows.caller_telescope (Q : UnitArrows)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HC : CallerCanonicalTelescope D (proofEraseCtx Γ)
      (B.inst (Q.canonical s uc)) n cs) :
    CallerCanonicalTelescope D (proofEraseCtx Γ) (.forallE (Q.raw s) B)
      (n+1) (Q.canonical s uc :: cs) := by
  have hQ : env.HasType univs Γ (Q.control U).expr (.sort (Q.control U).level) :=
    HeterogeneousControl.ControlType.typed Q.wf
  have SD : DomainSort (proofEraseCtx Γ) (Q.raw s) (Q.control U).level :=
    ⟨Γ, _, hΓ, rfl, hQ, Q.erase hi hS hΓ⟩
  have hp : ¬ (Q.control U).level ≈ .zero := by
    intro E
    exact (Q.control U).level_ne_zero [] (congrFun E [])
  exact CallerCanonicalTelescope.native_unit_profile heq hs hi rfl rfl rfl
    (Q.profile hi hS hΓ) SD hp HC

/-- The actual stored outer Pi supplies the selected native family header
in every ordinary context. Its codomain is arbitrary; its literal unit-arrow
domain can have any finite order. No semantic head-exposure premise is used. -/
theorem UnitArrows.stored_family_native (Q : UnitArrows)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants family = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.const family [])
      (.forallE (Q.raw s) (proofErase ((Q.control U).expr :: Γ) B)) := by
  have HF : env.HasType univs Γ (.const family []) (ci.type.instL []) :=
    HasType.const hc (by simp) (by simp [hU])
  rw [hT] at HF
  obtain ⟨_, HT⟩ := HF.isType henv hΓ
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.const family []) (proofErase Γ (ci.type.instL [])) := by
    have HF₀ : env.HasType univs [] (.const family []) (ci.type.instL []) :=
      HasType.const hc (by simp) (by simp [hU])
    obtain ⟨_, HT₀⟩ := HF₀.isType henv (by trivial)
    rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) HT₀ hΓ]
    exact ScopedTypeRecovery.const (ls := []) hc (by simp) (by simp [hU])
  rw [hT, show proofErase Γ (.forallE (Q.control U).expr B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ HT), Q.erase hi hS hΓ] at RN
  exact RN

/-- Arbitrary source computation and arbitrary raw substitution return to the
family at the canonical higher-order argument. Only the target family has a
native premise; no original or computed supplied argument has one. -/
theorem UnitArrows.family_substitution_return (Q : UnitArrows)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (ht : Target.Sound env univs)
    (hF : env.projections family info) (hlen : info.nparams + info.nindices = 1)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hΓ : OnCtx Γ (env.IsType univs))
    (hApp : env.HasType univs Γ₀ (VExpr.mkApps (.const family ls) args) (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ)
      (.const family ls) (.forallE (Q.raw s) B))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (VExpr.mkApps (.const family ls) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ)
      (out.subst σ) (.app (.const family ls) (Q.canonical s uc)) := by
  apply static_structure_registered_canonical_substitution_return (cs := [Q.canonical s uc]) (σ := σ) heq hs hF hD hΓ₀ hApp RN ?_ R
  rw [hlen]
  exact Q.caller_telescope hi hS heq ht hΓ .nil

/-- In the actual environment, arbitrary whole-family computation returns to
one canonical argument of any finite unit-arrow order. Stored declaration data
discharges all native and telescope premises. The supplied argument is arbitrary
and ordinarily typed only as part of the initial family application. -/
theorem UnitArrows.environment_stored_family_return (Q : UnitArrows)
    (heq : env.HasCanonicalEq)
    (hF : env.projections family info) (hlen : info.nparams + info.nindices = 1)
    (hc : env.constants family = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hApp : env.HasType univs Γ (VExpr.mkApps (.const family []) args) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const family []) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const family []) (Q.canonical s uc)) := by
  simpa only [ProofShape.subst_id] using Q.family_substitution_return hi hS
    (σ := Subst.id) heq EnvironmentCore.sound EnvironmentCore.sound hF hlen
    (EnvironmentCore.no_rigid (henv.projectionRigid hF)) hΓ hΓ hApp
    (Q.stored_family_native hi hS hΓ hc hU hT) R

/-- The concrete stored-header fragment repairs an arbitrary computation
before instantiation against an independent computation after instantiation.
The left branch may instantiate with any raw image, including an independently
computed argument. No relation to that image or native certificate for either
argument is needed. All native/profile premises are discharged from the actual declarations. -/
theorem UnitArrows.environment_stored_family_instantiation_fork (Q : UnitArrows)
    (heq : env.HasCanonicalEq)
    (hF : env.projections family info) (hlen : info.nparams + info.nindices = 1)
    (hc : env.constants family = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hApp : env.HasType univs (A :: Γ) (VExpr.mkApps (.const family []) args) (.sort u))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) (VExpr.mkApps (.const family []) args)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
      (proofEraseCtx Γ) (proofErase Γ ((VExpr.mkApps (.const family []) args).inst x)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        (left.inst image) (.app (.const family []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        right (.app (.const family []) (Q.canonical s uc)) := by
  apply static_structure_registered_canonical_instantiation_fork (cs := [Q.canonical s uc]) heq EnvironmentCore.sound EnvironmentCore.sound
    hF (EnvironmentCore.no_rigid (henv.projectionRigid hF))
    (EnvironmentCore.no_rigid (henv.projectionRigid hF)) hΓA hx hApp
    (Q.stored_family_native hi hS hΓA.1 hc hU hT) ?_ RL RR
  rw [hlen]
  exact Q.caller_telescope hi hS heq EnvironmentCore.sound hΓA.1 .nil

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
