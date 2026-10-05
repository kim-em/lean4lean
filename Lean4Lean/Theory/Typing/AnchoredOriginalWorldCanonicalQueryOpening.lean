import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQuerySiteReady
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryInitialProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldStaticCallBounds
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! A canonical opening must use the actual child query depths as its fuel.
Copying a caller's masked fuel into a lower-cutoff site does not establish
this property. These producers choose real closed original sites and derive
both child readiness and strict opening from the actual delta query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable def canonicalQueryControls
    {strata : EquationStratification env} (selected : strata.Selected rule)
    (children : Nat → Nat) : OriginalWorldControls strata selected.origin.source :=
  ⟨selected.origin.ordered, selected.ordinal - 1,
    Nat.le_trans (Nat.sub_le _ _) selected.ordinal_le, selected.sourceCutoff, children⟩

/-- An actual closed query can use the empty frame regardless of the caller's
substitution. This does not assert anything about its nested opening sites. -/
theorem WorldQuerySite.closedReference_ready
    {strata : EquationStratification env}
    (reference : EndpointRef sourceEnv U [] expression assigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (query : RichObs sourceEnv env U registry target (.ref reference) [] σ profile [])
    (below : sourceEnv ≤ env) :
    (WorldQuerySite.closedReference (registry := registry) (target := target)
      strata reference controls σ).Ready query := by
  refine ⟨below, ?_, .nil, ?_, ?_⟩
  · simpa only [WorldQuerySite.closedReference, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
      RawOriginalRichFrame.Ambient, and_true] using below
  · intro index need member
    cases member
  · intro index need member
    cases member

section Delta
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {value : VDefVal} {name : Name}
  {seedLevels levels : List VLevel} {atom : Atom n} {support : Profile n}
  {typeRealization bodyRealization : Subst}

noncomputable def legacyDeltaChildControls
    (registered : DefinitionRegistered env value)
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) []) :
    OriginalWorldControls strata (strata.select registered.2).origin.source :=
  canonicalQueryControls (strata.select registered.2)
    (fun control => max
      (body.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
      (certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))

theorem legacyDeltaChildControls_within
    (registered : DefinitionRegistered env value)
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) []) :
    let controls := legacyDeltaChildControls (strata := strata) registered certificate body
    EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => body.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) ∧
    EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) :=
  ⟨fun _ _ => Nat.le_max_left _ _, fun _ _ => Nat.le_max_right _ _⟩

theorem legacyDelta_opening
    (lookup : registry.definitions name = some value) (nameEq : value.name = name)
    (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = value.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (typed : (Profile.singleton atom).HasType support)
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) [])
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (caller : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (incoming : EquationStratifiedFuel.WithinAbove caller.cutoff caller.fuel
      (fun control => (Obs.delta (locals := locals) (σ := σ) lookup nameEq registered
        seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body).headDepth
          (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    let selected := strata.select registered.2
    let controls := legacyDeltaChildControls (strata := strata) registered certificate body
    WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental
        (.ref (.left (EquationHeaderOrigin.instantiatedType selected.origin seedWF))) .nil)
      (originalCallWorld caller .fundamental node captured) ∧
    WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs selected.origin seedWF))) .nil)
      (originalCallWorld caller .fundamental node captured) := by
  let selected := strata.select registered.2
  have bound : EquationStratifiedFuel.WithinAbove caller.cutoff caller.fuel
      (EquationStratifiedFuel.headDepth selected.ordinal
        (legacyDeltaChildControls (strata := strata) registered certificate body).fuel) := by
    intro control active
    have exactBound := incoming control active
    simpa only [Obs.headDepth, stratifiedHeadPolicy, strata.headOrdinal_definition lookup registered.2,
      legacyDeltaChildControls, canonicalQueryControls, EquationStratifiedFuel.headDepth, selected] using exactBound
  constructor <;> apply Below.root
    (EquationStratifiedFuel.openingDecrease selected.ordinal_pos selected.ordinal_le caller.cutoffBound bound _ _ _ _)
  all_goals intro child member; cases member

/-- The selected canonical RHS is immediately executable with the actual
body observer; its own fuel is computed from that observer and type code. -/
theorem legacyDelta_body_ready
    (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) []) :
    let selected := strata.select registered.2
    let controls := legacyDeltaChildControls (strata := strata) registered certificate body
    let reference := EndpointRef.left (EquationHeaderOrigin.instantiatedRhs selected.origin seedWF)
    (WorldQuerySite.closedReference (registry := registry) (target := target)
      strata reference controls bodyRealization).Ready (.legacy (.legacy body)) :=
  WorldQuerySite.closedReference_ready _ _ _ (strata.select registered.2).origin.sourceBelow

theorem legacyDelta_type_ready
    (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) []) :
    let selected := strata.select registered.2
    let controls := legacyDeltaChildControls (strata := strata) registered certificate body
    let reference := EndpointRef.left (EquationHeaderOrigin.instantiatedType selected.origin seedWF)
    (WorldQuerySite.closedReference (registry := registry) (target := target)
      strata reference controls typeRealization).Ready
        (.code (.legacy (.ofCode certificate certificate.formed))) :=
  WorldQuerySite.closedReference_ready _ _ _ (strata.select registered.2).origin.sourceBelow

end Delta
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
