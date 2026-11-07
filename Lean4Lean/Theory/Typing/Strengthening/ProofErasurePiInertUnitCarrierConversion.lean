import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierCoreConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout

/-! # Unit carriers survive guarded computation

Rigid-family readout removes administrative expansion by beta reduction. For a
nullary empty structure, the exposed family supplies a complete carrier history.
Ordinary-core confluence then retains all future typed substitutions and all
three independent residuals. The original guarded path need not transport under
substitution, and its stage does not bound the resulting carrier history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed raw carrier that beta-returns to a rigid nullary empty family has
a complete history at any requested stage. Endpoint shapes are unrestricted.
Future substitutions are supplied by the certified ordinary-core return path. -/
theorem pi_inert_beta_unit_carrier_history
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (HT : TypedSource Δ C) (R : BetaRed C (.const family ls)) :
    PiInertCarrierHistory D stage Δ C a b := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
  exact PiInertCarrierHistory.carrier_prefix (PiInertEvidence.core hs hc hΓ ht (.beta R))
    (pi_inert_unit_carrier_history hi hp hx hf hD)

/-- Every full-union computation of a typed nullary empty structure type
produces a complete unit-carrier history, already at stage zero if desired.
Function and structure eta, singleton rules, and administrative expansions are
allowed along the path; literal rigid-root preservation is not assumed. -/
theorem static_structure_computed_unit_carrier_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.const family ls)) out) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) out a b := by
  obtain ⟨ls', args', hn, RB⟩ :=
    RigidDemandProfile.static_structure_rigid_telescope_head_readout heq hs
      (henv.projectionRigid hi) hD hΓ hS (args := []) .sort .nil R
  have ha : args' = [] := by simpa using hn
  subst args'
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hS rfl rfl R
  exact pi_inert_beta_unit_carrier_history hs hc hi hp hx hf hD
    ⟨Γ, e, _, hΓ, rfl, HE.hasType.2, EE⟩ RB

/-- The restricted Pi-inert computation skeleton inherits the full-union
unit result. The output history stage is independent of the input path stage. -/
theorem pi_inert_computed_unit_carrier_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ (.const family ls)) out) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) out a b :=
  static_structure_computed_unit_carrier_history heq hs hc hi hp hx hf hD hΓ hS
    (R.mono (fun H => ⟨n, H.1⟩))

/-- A guarded common reduct transfers a unit history to a target carrier.
The old-to-shared path may use the full expanded union; the target-to-shared
path retains its actual computation certificate. This does not promote a
common comparison or bare semantic type equality to a directed path. -/
theorem pi_inert_unit_carrier_guarded_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (RS : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.const family ls)) shared)
    (RE : PiInertEvidence D stage .compute (proofEraseCtx Γ) E shared) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) E a b :=
  PiInertCarrierHistory.carrier_prefix RE
    (static_structure_computed_unit_carrier_history heq hs hc hi hp hx hf hD hΓ hS RS)

end Lean4Lean.VEnv.Strengthening
