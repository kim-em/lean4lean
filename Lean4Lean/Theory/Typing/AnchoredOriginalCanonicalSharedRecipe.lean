import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeSiteProducers
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaElimination

/-! Canonical code sites and their finite eliminations produce the shared rich
certificate syntax. Dependent body steps use the actual source frame to retain
its local layout; no new semantic answer is assumed by this embedding. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def CanonicalCodeSitePacket.toRecipe
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (source : List VExpr) (locals : List Nat) (σ : Subst) :
    RichCodeRecipe env U registry target source locals σ expression relevant profile [] :=
  .root source locals σ packet.owner packet.node packet.canonicalClosed packet.expressionEq
    packet.realization packet.certificate packet.resources

@[simp] theorem CanonicalCodeSitePacket.toRecipe_headDepth
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (policy : Name → Nat → Nat) :
    (packet.toRecipe source locals σ).headDepth policy =
      policy packet.name (packet.certificate.headDepth policy) := rfl

@[simp] theorem CanonicalCodeSitePacket.toRecipe_stratifiedDepth
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (control : Nat) :
    (packet.toRecipe source locals σ).stratifiedDepth (strata.headOrdinal registry) control =
      packet.chargeDepth control := by
  simp only [RichCodeRecipe.stratifiedDepth, packet.toRecipe_headDepth,
    stratifiedHeadPolicy, CanonicalCodeSitePacket.chargeDepth,
    CanonicalCodeOwner.headOrdinal_eq, RichCert.stratifiedDepth]

noncomputable def CanonicalCodeSitePacket.toRichCert
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) :
    RichCert sourceEnv env U registry target node locals σ relevant profile [] :=
  .recipe (packet.toRecipe source locals σ)

@[simp] theorem CanonicalCodeSitePacket.toRichCert_headDepth
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (policy : Name → Nat → Nat) :
    (packet.toRichCert node locals σ).headDepth policy =
      policy packet.name (packet.certificate.headDepth policy) := rfl

private theorem recipe_castLocals_depth
    {locals otherLocals : List Nat} (same : locals = otherLocals)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint)
    (rank : Name → Nat) (control : Nat) :
    (same ▸ recipe).stratifiedDepth rank control = recipe.stratifiedDepth rank control := by
  cases same
  rfl

/-- Retain the actual frame layout while embedding every dependent recipe
step. The equality concerns the same chosen shared recipe, including its root
certificate and every explicit binder demand. -/
noncomputable def CanonicalDeltaElimination.sharedRecipe
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    {code : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint //
      ∀ control, code.stratifiedDepth (strata.headOrdinal registry) control = recipe.depth control} := by
  induction recipe generalizing sourceEnv locals τ available with
  | root source σ packet =>
    refine ⟨packet.codeSite.toRecipe source locals σ, ?_⟩
    intro control
    simpa only [CanonicalDeltaElimination.depth, packet.codeSite_chargeDepth] using
      packet.codeSite.toRecipe_stratifiedDepth source locals σ control
  | domain parent ih =>
    obtain ⟨code, depth⟩ := ih frame
    exact ⟨.domain code, depth⟩
  | fixedBody parent selected admitted ih =>
    obtain ⟨code, depth⟩ := ih frame
    exact ⟨.fixedBody code selected admitted, depth⟩
  | action change parent ih =>
    obtain ⟨code, depth⟩ := ih frame
    exact ⟨.action change code, depth⟩
  | body parent selected anchor ih =>
    cases context with
    | cons context domain =>
      obtain ⟨code, depth⟩ := ih frame.fullTail.frame
      refine ⟨frame.fullTail.positions ▸ (.body code selected anchor), ?_⟩
      intro control
      rw [recipe_castLocals_depth]
      exact depth control

noncomputable def CanonicalDeltaElimination.toRichCert
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (node : EndpointState sourceEnv U source expression assigned) :
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint :=
  .recipe (recipe.sharedRecipe frame).val

@[simp] theorem CanonicalDeltaElimination.toRichCert_stratifiedDepth
    (recipe : CanonicalDeltaElimination env U registry target strata source σ expression relevant profile footprint)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (node : EndpointState sourceEnv U source expression assigned) (control : Nat) :
    (recipe.toRichCert frame node).stratifiedDepth (strata.headOrdinal registry) control =
      recipe.depth control :=
  (recipe.sharedRecipe frame).property control

end Lean4Lean.AnchoredSource.Adapted
