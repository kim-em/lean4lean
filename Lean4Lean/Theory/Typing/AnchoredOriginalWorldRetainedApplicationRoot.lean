import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationBody
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantOpening

/-! Execute the literal application input of a charged root. The ordinal
opening funds the actual source program, whose physical operands are then
proper original children. No returned F certificate becomes recursive input.
Level alignment is retained separately: the result is at the source program,
not an assertion that its operands already belong to the caller frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem executeCanonicalApplicationInputWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] (.app f a) (.sort level))
    (provenance : EndpointProvenance .nil node)
    (realization : Subst)
    (certificate : RichCert owner.selected.origin.source env U registry target node
      [] realization relevant profile footprint)
    (child : WorldCertProvenance strata certificate)
    (resources : footprint.Available (fun _ => []))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (childPaid : Sponsored frontier child.worlds)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ profile.atoms) :
    let sourceControls := canonicalQueryControls owner.selected
      (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control)
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target [] [] realization f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available (fun _ => []) ∧ children.worlds ⊆ child.worlds ∧
      origin.RootedAt node ∧ (∀ policy, origin.headDepth policy ≤ certificate.headDepth policy) ∧
      Nonempty (RetainedApplicationStep sourceControls frontier realization (fun _ => []) origin) := by
  dsimp only
  let fuel := fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control
  let sourceControls := canonicalQueryControls owner.selected fuel
  let frame : OriginalRichFrame owner.selected.origin.source env U registry target .nil
      [] realization realization (fun _ => []) := .nil
  obtain ⟨data, paid, lowerBank⟩ := canonicalNilOpeningBank (registry := registry) (target := target)
    owner node realization fuel caller controls baseline frontier callerPaid sourceReady masked bank
  let ready : ControlledStoredQuery sourceControls frontier (.certificate certificate) := {
    annotation := child
    within := fun _ _ => Nat.le_refl _
    sponsored := childPaid }
  exact ready.executeRetainedApplication provenance frame .nil data
    (fun _ _ member => nomatch member) formed .nil resources henv hscoped
    owner.selected.origin.sourceBelow paid lowerBank selected

/-- The shared root annotation supplies the exact child and its sponsors.
The caller does not supply either operand answer or a new source bank. -/
theorem WorldCodeRecipeProvenance.executeRootApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {owner : CanonicalCodeOwner env registry strata name}
    {node : EndpointState owner.selected.origin.source U [] (.app f a) (.sort level)}
    {certificate : RichCert owner.selected.origin.source env U registry target node
      [] realization relevant profile footprint}
    {resources : footprint.Available (fun _ => [])}
    (annotation : WorldCodeRecipeProvenance strata
      (.root source locals σ owner node closed expressionEq realization certificate resources))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => (RichCodeRecipe.root source locals σ owner node closed expressionEq
        realization certificate resources).stratifiedDepth (strata.headOrdinal registry) control))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ profile.atoms) :
    let sourceControls := canonicalQueryControls owner.selected
      (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control)
    ∃ provenance : EndpointProvenance .nil node,
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target [] [] realization f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available (fun _ => []) ∧ children.worlds ⊆ annotation.worlds ∧
      origin.RootedAt node ∧ (∀ policy, origin.headDepth policy ≤ certificate.headDepth policy) ∧
      Nonempty (RetainedApplicationStep sourceControls frontier realization (fun _ => []) origin) := by
  cases annotation with
  | root source locals σ owner node closed expressionEq realization certificate resources child oldControls provenance =>
    have masked : WithinAbove controls.cutoff controls.fuel
        (headDepth owner.selected.ordinal
          (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control)) := by
      intro control active
      simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth,
        stratifiedHeadPolicy, owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using bounded control active
    obtain ⟨origin, children, path, supplied, included, rooted, depth, step⟩ :=
      executeCanonicalApplicationInputWorld owner node provenance realization certificate child resources
        caller controls baseline frontier callerPaid sourceReady
        (fun world member => sponsored world (List.mem_append_right _ member)) masked bank
        henv hscoped formed selected
    exact ⟨provenance, origin, children, path, supplied,
      fun world member => List.mem_append_right _ (included member), rooted, depth, step⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
