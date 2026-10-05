import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOccurrenceSites
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryInitialProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrences
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorMeasure

/-! Contextual initial provenance uses the actual framed source traversal.
The world ledger below is the exact semantic frame environment, never the
possibly larger location-bound environment. Fresh binder annotations retain
the original domain selected by the original location. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable def OriginalRichOccurrenceFrame.piAnchorWorld
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.pi hu hv domain body)}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    WorldEnvironmentProvenance strata U
      ((occurrence.piAnchor henv sourceBelow certificate resources guard pack covered).frame.dependencyEnvironment controls.ordered) := by
  change WorldEnvironmentProvenance strata U
    (.close ((Classical.choose location.originalDomains.1).dependencyOrigin controls.ordered)
      (occurrence.frame.dependencyEnvironment controls.ordered) :: occurrence.frame.dependencyEnvironment controls.ordered)
  exact .cons (.original (.ref (Classical.choose location.originalDomains.1)) controls environment) environment

noncomputable def OriginalRichOccurrenceFrame.lamAnchorWorld
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    WorldEnvironmentProvenance strata U
      ((occurrence.lamAnchor henv sourceBelow certificate resources guard pack covered).frame.dependencyEnvironment controls.ordered) := by
  change WorldEnvironmentProvenance strata U
    (.close ((Classical.choose location.originalDomains.1).dependencyOrigin controls.ordered)
      (occurrence.frame.dependencyEnvironment controls.ordered) :: occurrence.frame.dependencyEnvironment controls.ordered)
  exact .cons (.original (.ref (Classical.choose location.originalDomains.1)) controls environment) environment

/-- A retained declaration location receives the actual current frame. Its
original-context equation, rather than a fresh reserve assumption, proves the
location budget. This is the entry point for native declaration-plan children. -/
noncomputable def OriginalRichFrame.declarationOccurrence
    {header : EndpointRef sourceEnv U [] headerExpression headerType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located header node)
    {context : ContextDerivation sourceEnv U source}
    (lineage : location.contextDerivation .nil = context)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (exactEnvironment : frame.dependencyEnvironment ordered = context.dependencyClosures ordered) :
    OriginalRichOccurrenceFrame location .nil env registry target locals σ τ available ordered [] := by
  subst context
  exact ⟨frame, substitutions, by
    rw [exactEnvironment, location.contextDerivation_dependencyClosures]
    exact Nat.le_refl _⟩

/-- The declaration transport preserves the computed environment exactly. -/
theorem OriginalRichFrame.declarationOccurrence_environment
    {header : EndpointRef sourceEnv U [] headerExpression headerType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located header node)
    {context : ContextDerivation sourceEnv U source}
    (lineage : location.contextDerivation .nil = context)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (exactEnvironment : frame.dependencyEnvironment ordered = context.dependencyClosures ordered) :
    (frame.declarationOccurrence location lineage ordered substitutions exactEnvironment).frame.dependencyEnvironment ordered =
      frame.dependencyEnvironment ordered := by
  subst context
  rfl

/-- Exact declaration-plan frame, including its original context ledger. -/
structure WorldPlanFrame (strata : EquationStratification env)
    (context : ContextDerivation sourceEnv U source) (registry : CanonicalHead.Registry)
    (target : List VExpr) (arguments : List VExpr) (σ : Subst) where
  controls : OriginalWorldControls strata sourceEnv
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context (List.range arguments.length) σ σ available
  substitutions : Ctx.SubstEq env U target σ σ source
  exactEnvironment : frame.dependencyEnvironment controls.ordered = context.dependencyClosures controls.ordered
  environment : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)

noncomputable def WorldPlanFrame.nil
    {strata : EquationStratification env} (controls : OriginalWorldControls strata sourceEnv) (σ : Subst) :
    WorldPlanFrame (U := U) strata (.nil : ContextDerivation sourceEnv U []) registry target [] σ :=
  ⟨controls, (fun _ => []), .nil, .nil, rfl, .nil⟩

noncomputable def WorldPlanFrame.occurrence
    {strata : EquationStratification env}
    {header : EndpointRef sourceEnv U [] headerExpression headerType}
    {node : EndpointState sourceEnv U source expression assigned}
    {context : ContextDerivation sourceEnv U source}
    (world : WorldPlanFrame strata context registry target arguments σ)
    (location : Located header node) (lineage : location.contextDerivation .nil = context) :
    OriginalRichOccurrenceFrame location .nil env registry target (List.range arguments.length) σ σ world.available
      world.controls.ordered [] :=
  world.frame.declarationOccurrence location lineage world.controls.ordered world.substitutions world.exactEnvironment

noncomputable def WorldPlanFrame.occurrenceWorld
    {strata : EquationStratification env}
    {header : EndpointRef sourceEnv U [] headerExpression headerType}
    {node : EndpointState sourceEnv U source expression assigned}
    {context : ContextDerivation sourceEnv U source}
    (world : WorldPlanFrame strata context registry target arguments σ)
    (location : Located header node) (lineage : location.contextDerivation .nil = context) :
    WorldEnvironmentProvenance strata U
      ((world.occurrence location lineage).frame.dependencyEnvironment world.controls.ordered) :=
  (world.frame.declarationOccurrence_environment location lineage world.controls.ordered
    world.substitutions world.exactEnvironment).symm ▸ world.environment

private theorem localsCast_environment
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (equal : locals = nextLocals) (ordered : sourceEnv.Ordered) :
    (equal ▸ frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases equal
  rfl

noncomputable def WorldPlanFrame.push
    {strata : EquationStratification env} {context : ContextDerivation sourceEnv U source}
    (world : WorldPlanFrame strata context registry target arguments σ)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (original : EndpointRef sourceEnv U source domain (.sort level))
    (certificate : RichCert sourceEnv env U registry target (.ref original) (List.range arguments.length)
      σ true (support : Profile n) domainFootprint)
    (resources : domainFootprint.Available world.available)
    (guard : LambdaGuard env U registry target σ domain key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    WorldPlanFrame strata (.cons context original) registry target (arguments ++ [key.anchor]) (σ.cons key.anchor) := by
  have related : Related env U registry target key.anchor key.anchor (domain.subst σ) key.input support := by
    obtain ⟨_, _, _, _, _, _, _, arguments⟩ := guard.anchor
    exact Related.convert henv guard.inputTyped guard.domains arguments
  let child := OriginalRichFrame.bind world.frame original certificate resources guard.inputTyped related
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member => List.Subset.trans (pack.atomized_localNeeds need member).2 covered)
  have localEq : List.range (arguments ++ [key.anchor]).length = Locals.push (List.range arguments.length) := by
    simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
  refine ⟨world.controls, _, localEq.symm ▸ child,
    .cons world.substitutions (original.sound.defeq.mono below) (guard.path.cast guard.anchor.1), ?_, ?_⟩
  · change (localEq.symm ▸ child).dependencyEnvironment world.controls.ordered = _
    rw [localsCast_environment]
    change Closure.close (original.dependencyOrigin world.controls.ordered) (world.frame.dependencyEnvironment world.controls.ordered) ::
      world.frame.dependencyEnvironment world.controls.ordered = _
    rw [world.exactEnvironment]
    rfl
  · rw [localsCast_environment]
    exact .cons (.original (.ref original) world.controls world.environment) world.environment

private def contextualControls (strata : EquationStratification env)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (fuel : Nat → Nat) :
    OriginalWorldControls strata sourceEnv :=
  ⟨ordered, strata.rules.length, Nat.le_refl _, strata.fullCutoff.source_mono below, fuel⟩

private noncomputable def closedOccurrence
    (reference : EndpointRef sourceEnv U [] expression assigned) (ordered : sourceEnv.Ordered) (σ : Subst) :
    OriginalRichOccurrenceFrame (.here (root := reference)) .nil env registry target [] σ σ (fun _ => []) ordered [] :=
  ⟨.nil, .nil, Nat.le_refl _⟩

mutual
noncomputable def RichCert.contextualWorldProvenance
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (below : sourceEnv ≤ env) (resources : footprint.Available available) :
    WorldCertProvenance strata certificate := by
  match certificate with
  | .legacy child =>
    exact .legacy child (SortableCert.initialWorldProvenance strata henv controls.fuel child)
  | .observe child formed =>
    exact .observe (child.contextualWorldProvenance controls occurrence environment henv below resources) formed
  | .pi hu hv domain guard rows =>
    let dr := fun i need member => resources i need (List.mem_append_left _ member)
    exact .pi hu hv domain guard rows
      (domain.contextualWorldProvenance controls occurrence.piDomain environment henv below dr)
      (rows.contextualWorldProvenance hu hv controls occurrence environment domain dr henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
  | .route route child =>
    exact .route route (child.contextualWorldProvenance controls
      (occurrence.route route) (occurrence.routeWorld controls route environment) henv below resources)
  | .union first second =>
    exact .union
      (first.contextualWorldProvenance controls occurrence environment henv below
        (fun i need member => resources i need (List.mem_append_left _ member)))
      (second.contextualWorldProvenance controls occurrence environment henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
  | .pad child =>
    exact .pad (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .down child =>
    exact .down (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .map change child =>
    exact .map change (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .support change child =>
    exact .support change (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .select child member =>
    exact .select (child.contextualWorldProvenance controls occurrence environment henv below resources) member
termination_by structural certificate

noncomputable def RichRows.contextualWorldProvenance
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U context A (.sort u)}
    {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint)
    (hu : u.WF U) (hv : v.WF U)
    {location : Located root (.pi hu hv domain body)}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (henv : env.Ordered) (below : sourceEnv ≤ env) (resources : footprint.Available available) :
    WorldRowsProvenance strata rows := by
  match rows with
  | .nil =>
    exact .nil
  | .cons guard certificate pack covered tail =>
    exact .cons guard certificate pack covered tail
      (certificate.contextualWorldProvenance controls
        (occurrence.piAnchor henv below domainCode domainResources guard pack covered)
        (occurrence.piAnchorWorld controls environment henv below domainCode domainResources guard pack covered)
        henv below (pack.available_atomized_localNeeds
          (fun i need member => resources i need (List.mem_append_left _ member))))
      (tail.contextualWorldProvenance hu hv controls occurrence environment domainCode domainResources henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
termination_by structural rows

noncomputable def RichObs.contextualWorldProvenance
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (below : sourceEnv ≤ env) (resources : footprint.Available available) :
    WorldObsProvenance strata query := by
  match query with
  | .legacy child =>
    exact .legacy child (SortableObs.initialWorldProvenance strata henv controls.fuel child)
  | .code child =>
    exact .code (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .projection head nameEq member major field typed alignment =>
    let routeWorld := occurrence.routeWorld controls head.route environment
    exact .projection head nameEq member
      (major.contextualWorldProvenance controls (occurrence.projMajor head) routeWorld henv below
        (fun i need member => resources i need (List.mem_append_left _ member)))
      (field.contextualWorldProvenance controls (occurrence.projField head) routeWorld henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
      ((occurrence.projMajor head).worldSite controls routeWorld)
      ((occurrence.projField head).worldSite controls routeWorld) typed alignment
  | .projectionSortable head nameEq member major selected path sortable field typed =>
    let routeWorld := occurrence.routeWorld controls head.route environment
    exact .projectionSortable head nameEq member selected path sortable
      (major.contextualWorldProvenance controls (occurrence.projMajor head) routeWorld henv below
        (fun i need member => resources i need (List.mem_append_left _ member)))
      (field.contextualWorldProvenance controls (occurrence.projField head) routeWorld henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
      ((occurrence.projMajor head).worldSite controls routeWorld)
      ((occurrence.projField head).worldSite controls routeWorld) typed
  | .app hu hv fn arg adapter admitted =>
    exact .app hu hv
      (fn.contextualWorldProvenance controls occurrence.appFunction environment henv below
        (fun i need member => resources i need (List.mem_append_left _ member)))
      (arg.contextualWorldProvenance controls occurrence.appArgument environment henv below
        (fun i need member => resources i need (List.mem_append_right _ member))) adapter admitted
  | .lam hu hv domain guard body pack covered =>
    let dr := fun i need member => resources i need (List.mem_append_left _ member)
    exact .lam hu hv domain guard body pack covered
      (domain.contextualWorldProvenance controls occurrence.lamDomain environment henv below dr)
      (body.contextualWorldProvenance controls (occurrence.lamAnchor henv below domain dr guard pack covered)
        (occurrence.lamAnchorWorld controls environment henv below domain dr guard pack covered)
        henv below (pack.available_atomized_localNeeds
          (fun i need member => resources i need (List.mem_append_right _ member))))
  | .route route child =>
    exact .route route (child.contextualWorldProvenance controls
      (occurrence.route route) (occurrence.routeWorld controls route environment) henv below resources)
  | .union first second =>
    exact .union
      (first.contextualWorldProvenance controls occurrence environment henv below
        (fun i need member => resources i need (List.mem_append_left _ member)))
      (second.contextualWorldProvenance controls occurrence environment henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
  | .view child change =>
    exact .view (child.contextualWorldProvenance controls occurrence environment henv below resources) change
  | .action child change =>
    exact .action (child.contextualWorldProvenance controls occurrence environment henv below resources) change
  | .select child member =>
    exact .select (child.contextualWorldProvenance controls occurrence environment henv below resources) member
  | .pad child =>
    exact .pad (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .unpad child =>
    exact .unpad (child.contextualWorldProvenance controls occurrence environment henv below resources)
  | .family (typeRealization := typeRealization) (planRealization := planRealization)
      origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    let headerControls := contextualControls strata origin.ordered (origin.sourceBelow.trans below) controls.fuel
    exact .family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree
      (certificate.contextualWorldProvenance headerControls (closedOccurrence _ origin.ordered typeRealization) .nil henv
        (origin.sourceBelow.trans below) (by intro _ _ member; cases member))
      (tree.contextualWorldProvenance (WorldPlanFrame.nil headerControls planRealization) henv
        (origin.sourceBelow.trans below) (by intro _ _ member; cases member))
      (WorldQuerySite.closedReference strata _ headerControls typeRealization)
  | .constructor (typeRealization := typeRealization) (planRealization := planRealization)
      origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    let headerControls := contextualControls strata origin.ordered (origin.sourceBelow.trans below) controls.fuel
    exact .constructor origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree
      (certificate.contextualWorldProvenance headerControls (closedOccurrence _ origin.ordered typeRealization) .nil henv
        (origin.sourceBelow.trans below) (by intro _ _ member; cases member))
      (tree.contextualWorldProvenance (WorldPlanFrame.nil headerControls planRealization) henv
        (origin.sourceBelow.trans below) (by intro _ _ member; cases member))
      (WorldQuerySite.closedReference strata _ headerControls typeRealization)
termination_by structural query

noncomputable def RichFamilyPlan.contextualWorldProvenance
    {strata : EquationStratification env}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation sourceEnv U source}
    (tree : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint)
    (world : WorldPlanFrame strata context registry target arguments σ)
    (henv : env.Ordered) (below : sourceEnv ≤ env) (resources : footprint.Available world.available) :
    WorldFamilyPlanProvenance strata tree := by
  match tree with
  | .terminal saturated resultSort relevance captures =>
    exact .terminal saturated resultSort relevance captures
      (FamilyCaptures.initialWorldProvenance strata henv world.controls.fuel captures)
  | .binder domainOrigin original location lineage domainCode guard body pack covered =>
    let dr := fun i need member => resources i need (List.mem_append_left _ member)
    let child := world.push henv below original domainCode dr guard pack covered
    exact .binder domainOrigin original location lineage domainCode guard body pack covered
      (domainCode.contextualWorldProvenance world.controls (world.occurrence location lineage)
        (world.occurrenceWorld location lineage) henv below dr)
      (body.contextualWorldProvenance child henv below
        (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))))
  | .view child change =>
    exact .view child change (child.contextualWorldProvenance world henv below resources)
  | .pad child =>
    exact .pad child (child.contextualWorldProvenance world henv below resources)
termination_by structural tree

noncomputable def RichConstructorPlan.contextualWorldProvenance
    {strata : EquationStratification env}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation sourceEnv U source}
    (tree : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint)
    (world : WorldPlanFrame strata context registry target arguments σ)
    (henv : env.Ordered) (below : sourceEnv ≤ env) (resources : footprint.Available world.available) :
    WorldConstructorPlanProvenance strata tree := by
  match tree with
  | .terminal saturated resultShape relevant node location lineage captures resultCode =>
    exact .terminal saturated resultShape relevant node location lineage captures resultCode
      (FamilyCaptures.initialWorldProvenance strata henv world.controls.fuel captures)
      (resultCode.contextualWorldProvenance world.controls (world.occurrence location lineage)
        (world.occurrenceWorld location lineage) henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
  | .terminalRecord registered lookup nameEq bounded saturated resultShape node location lineage captures resultCode origins =>
    exact .terminalRecord registered lookup nameEq bounded saturated resultShape node location lineage captures resultCode origins
      (FamilyCaptures.initialWorldProvenance strata henv world.controls.fuel captures)
      (resultCode.contextualWorldProvenance world.controls (world.occurrence location lineage)
        (world.occurrenceWorld location lineage) henv below
        (fun i need member => resources i need (List.mem_append_right _ member)))
  | .binder domainOrigin original location lineage domainCode guard body pack covered =>
    let dr := fun i need member => resources i need (List.mem_append_left _ member)
    let child := world.push henv below original domainCode dr guard pack covered
    exact .binder domainOrigin original location lineage domainCode guard body pack covered
      (domainCode.contextualWorldProvenance world.controls (world.occurrence location lineage)
        (world.occurrenceWorld location lineage) henv below dr)
      (body.contextualWorldProvenance child henv below
        (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))))
  | .view child change =>
    exact .view child change (child.contextualWorldProvenance world henv below resources)
  | .pad child =>
    exact .pad child (child.contextualWorldProvenance world henv below resources)
termination_by structural tree
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
