import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationRoot
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeFocusedOpening

/-! An application root may be surrounded by arbitrary finite code actions
and resource-transfer wrappers. These wrappers are executed as a selected
output path; they never allocate a replacement recipe for recursive descent.
Pi eliminations are excluded by an explicit syntax predicate, not silently
assumed to be root-preserving. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private WorldCodeRecipeProvenance.focusExecutableInput from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeFocusedOpening
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def RichCodeRecipe.RootOnly
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) : Prop :=
  match recipe with
  | .root .. => True
  | .domain .. | .body .. | .fixedBody .. => False
  | .resources parent _ => parent.RootOnly
  | .action _ parent => parent.RootOnly

theorem RichRecipeContext.rootOnly_expression
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe) (onlyRoot : recipe.RootOnly) :
    input.expression = expression := by
  induction pending with
  | root => rfl
  | domain => cases onlyRoot
  | body => cases onlyRoot
  | fixedBody => cases onlyRoot
  | resources pending transfer ih => exact ih onlyRoot
  | action pending change ih => exact ih onlyRoot

theorem RichRecipeContext.rootOnly_output
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe) (onlyRoot : recipe.RootOnly)
    (selected : atom ∈ profile.atoms) :
    ∃ rootAtom ∈ input.profile.atoms,
      Nonempty (GeneralOutputPath env U registry target rootAtom atom) := by
  induction pending with
  | root => exact ⟨atom, selected, ⟨.refl⟩⟩
  | domain => cases onlyRoot
  | body => cases onlyRoot
  | fixedBody => cases onlyRoot
  | resources pending transfer ih => exact ih onlyRoot selected
  | @action nextRelevant m nextProfile source locals σ expression relevant n profile footprint parent pending change ih =>
    obtain ⟨previous, member, ⟨action⟩⟩ := change.atom selected
    obtain ⟨rootAtom, present, ⟨path⟩⟩ := ih onlyRoot member
    exact ⟨rootAtom, present, ⟨.code path action (parent.formed.singleton_of_mem member)⟩⟩

private noncomputable def appendApplicationOutput
    (first : GeneralOutputPath env U registry target a b)
    (second : GeneralOutputPath env U registry target b c) :
    GeneralOutputPath env U registry target a c := by
  induction second with
  | refl => exact first
  | action path change ih => exact .action ih change
  | code path change formed ih => exact .code ih change formed
  | pad path ih => exact .pad ih
  | unpad path ih => exact .unpad ih

/-- Root-only selection traverses the same annotated input. The resulting
source application may have different universe syntax from the caller;
`functionLevels` and `argumentLevels` retain that exact distinction. -/
theorem WorldCodeRecipeProvenance.executeRootOnlyApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {recipe : RichCodeRecipe env U registry target source locals σ (.app f a) relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (onlyRoot : recipe.RootOnly)
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sources : annotation.Sources P)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ profile.atoms) :
    ∃ input : RichRecipeRootInput env U registry target,
    ∃ pending : RichRecipeContext input recipe,
      sizeOf input.certificate < sizeOf recipe ∧
      ∃ same : input.strata = strata,
      ∃ canonicalFunction canonicalArgument,
      EqUpToLevels U canonicalFunction f ∧ EqUpToLevels U canonicalArgument a ∧
      ∃ node : EndpointState input.owner.selected.origin.source U []
          (.app canonicalFunction canonicalArgument) (.sort input.level),
      ∃ certificate : RichCert input.owner.selected.origin.source env U registry target node
          [] input.realization input.relevant input.profile input.footprint,
      HEq node input.node ∧ HEq certificate input.certificate ∧
      let sourceControls := canonicalQueryControls input.owner.selected
        (fun control => certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
      ∃ provenance : EndpointProvenance .nil node,
      ∃ origin : RetainedApplicationOrigin provenance.root env registry target [] []
        input.realization canonicalFunction canonicalArgument,
      ∃ children : RetainedApplicationWorlds input.strata origin,
        Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
        origin.footprint.Available (fun _ => []) ∧
        children.worlds ⊆ (same.symm ▸ annotation.worlds) ∧
        origin.RootedAt node ∧ (∀ policy, origin.headDepth policy ≤ certificate.headDepth policy) ∧
        Nonempty (RetainedApplicationStep sourceControls (same.symm ▸ frontier)
          input.realization (fun _ => []) origin) := by
  obtain ⟨input, ⟨pending⟩, smaller, same, sourceReady, child, oldControls, provenance, included⟩ :=
    WorldCodeRecipeProvenance.focusExecutableInput annotation sources
  have expressionShape := pending.rootOnly_expression onlyRoot
  have levelEq : EqUpToLevels U input.canonicalExpression (.app f a) := expressionShape ▸ input.expressionEq
  obtain ⟨rootAtom, rootMember, ⟨outputPath⟩⟩ := pending.rootOnly_output onlyRoot selected
  cases same
  have masked : WithinAbove controls.cutoff controls.fuel
      (headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have rootDepth := pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)
    have bound := Nat.le_trans rootDepth (bounded control active)
    simpa only [RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using bound
  cases input with
  | mk strata name owner expression canonicalExpression level node closed expressionEq source locals
      substitution realization relevant rank profile footprint certificate resources =>
    cases levelEq with
    | app functionLevels argumentLevels =>
      let input : RichRecipeRootInput env U registry target :=
        ⟨strata, name, owner, expression, _, level, node, closed, expressionEq, source,
          locals, substitution, realization, relevant, rank, profile, footprint, certificate, resources⟩
      obtain ⟨origin, children, ⟨path⟩, supplied, worlds, rooted, depth, step⟩ :=
        executeCanonicalApplicationInputWorld input.owner input.node provenance input.realization
          input.certificate child input.resources caller controls baseline frontier callerPaid sourceReady
          (fun world member => sponsored world (included (List.mem_append_right _ member)))
          masked bank henv hscoped formed rootMember
      exact ⟨input, pending, smaller, rfl, _, _, functionLevels, argumentLevels,
        input.node, input.certificate, HEq.rfl, HEq.rfl, provenance, origin, children, ⟨appendApplicationOutput path outputPath⟩, supplied,
        (fun world member => included (List.mem_append_right _ (worlds member))), rooted, depth, step⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
