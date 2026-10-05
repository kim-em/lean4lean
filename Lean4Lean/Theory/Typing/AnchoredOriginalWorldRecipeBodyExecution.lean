import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeCallBank

/-! Enter a retained native body without replacing its program by the result
of a fundamental call. The original domain call constructs the paired binder
frame. The original body certificate, its controls, and a strictly lower bank
are retained together for the next pending recipe operation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- This state contains the actual original body program, by its `row` index.
The selected semantic frame is computed; it does not contain a body answer. -/
structure RichPiRowBodyExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body key result)
    (τ : Subst) (anchor : VExpr)
    (hu : u.WF U) (hv : v.WF U)
    (parentEnvironment : WorldEnvironmentProvenance strata U environment) where
  frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain)
    (Locals.push locals) (σ.cons key.anchor) (τ.cons anchor)
    (Valuation.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) available)
  captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)
  environment_eq : HEq captured (reservedBindWorldEnvironment controls domain parentEnvironment parentEnvironment)
  data : WorldUnaryFrameData P controls frontier frame captured
  closed : (Valuation.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) available).AtomClosed
  substitutions : Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons anchor) (A :: source)
  resources : row.bodyFootprint.Available
    (Valuation.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) available)
  provenance : EndpointProvenance (.cons context domain) body
  ready : ControlledStoredQuery controls frontier (.certificate row.body)
  below : WorldBelow strata.rules.length (originalCallWorld controls .fundamental body captured)
    (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) parentEnvironment)
  sponsored : Sponsored frontier [originalCallWorld controls .fundamental body captured]
  bank : WorldBoundedUnaryCallBank env U registry strata P
    (frontier ++ [originalCallWorld controls .fundamental body captured])

/-- Interpret only the original domain. In particular, the next cursor is
`row.body`, rather than any query reconstructed by a body F call. The tail
realizations may differ: earlier pending body operations are retained. -/
theorem RichPiRowCertificate.enterBodyWorldExact
    {anchor : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured,
      execution.ready = ready.body := by
  have funding := piRowWorldFunding controls domain body hu hv captured frontier
  have children := piRowWorldChildren controls domain body hu hv captured
  obtain ⟨domainAnswer, _⟩ := worldCode controls frame captured frontier _ bank funding.1
    (singletonSponsoredBelow sponsored children.1) (.ofLocation domainLocation initial) data
    henv hscoped closed formed substitutions row.domain row.domainAvailable ready.domain
  have declared : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, paired, _⟩ := declared
  have arguments := Related.retag henv row.inputTyped domainAnswer.related.left_diagonal paired
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  let bodyFrame := (OriginalRichFrame.bind frame domain row.domain row.domainAvailable
    row.inputTyped arguments needs bounded covered).reserve
      [.close (domain.dependencyOrigin controls.ordered) (frame.dependencyEnvironment controls.ordered)]
  let bodyCaptured : WorldEnvironmentProvenance strata U (bodyFrame.dependencyEnvironment controls.ordered) :=
    reservedBindWorldEnvironment controls domain captured captured
  obtain ⟨bodyData⟩ := data.bind substitutions domain row.domain row.domainAvailable row.inputTyped
    arguments needs bounded covered ready.domain (atomizedNeeds_closed _)
  have pairedSubstitutions : Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons anchor) (A :: source) :=
    .cons substitutions (domain.sound.defeq.mono sourceBelow) raw
  have bodyProvenance : EndpointProvenance (.cons (domainLocation.contextDerivation initial) domain) body :=
    bodyContext ▸ EndpointProvenance.ofLocation bodyLocation initial
  refine ⟨⟨bodyFrame, bodyCaptured, HEq.rfl, bodyData,
    Valuation.push_atomized_closed closed _, pairedSubstitutions,
    row.pack.available_atomized_localNeeds row.outsideAvailable, bodyProvenance, ready.body,
    children.2, singletonSponsoredBelow sponsored children.2, ?_⟩, rfl⟩
  intro retained lower
  exact bank retained (lower.trans funding.2)

/-- Compatibility entry retaining the same actual body execution. -/
theorem RichPiRowCertificate.enterBodyWorld
    {anchor : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured) := by
  obtain ⟨execution, _⟩ := row.enterBodyWorldExact initial henv hscoped sourceBelow controls domain domainLocation body bodyLocation
    bodyContext hu hv frame captured frontier data bank sponsored closed formed substitutions
    ready admitted
  exact ⟨execution⟩

/-- Execute the actual pending row program, including mixed rank input and
anchor changes, before entering the literal stored body. No admission at the
old key is supplied: it is computed from the real row guard. -/
theorem RankedPendingNativeRow.enterBodyWorld
    {anchor : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {table : List (Key n × Profile n)} {selectedKey : Key m} {selectedResult : Profile m}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      pending.oldKey pending.oldResult)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target selectedKey anchor anchor) :
    Nonempty (RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured) := by
  exact row.enterBodyWorld initial henv hscoped sourceBelow controls domain domainLocation body bodyLocation
    bodyContext hu hv frame captured frontier data bank sponsored closed formed substitutions ready
    (pending.oldAdmission henv hscoped formed row.anchor admitted)

/-- Ranked pending entry preserves the literal selected body annotation. -/
theorem RankedPendingNativeRow.enterBodyWorldExact
    {anchor : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {table : List (Key n × Profile n)} {selectedKey : Key m} {selectedResult : Profile m}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      pending.oldKey pending.oldResult)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target selectedKey anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured,
      execution.ready = ready.body := by
  exact row.enterBodyWorldExact initial henv hscoped sourceBelow controls domain domainLocation body bodyLocation
    bodyContext hu hv frame captured frontier data bank sponsored closed formed substitutions ready
    (pending.oldAdmission henv hscoped formed row.anchor admitted)

/-- The actual `.body` instruction obtains its selected admission from the
same caller binder resource. The parent recipe is interpreted through the
caller bank; the retained native body is entered through the source bank.
Both banks are internal original-call induction hypotheses, not code answers.
The resulting semantic body relation and execution frame belong to the same
selected instruction. -/
theorem WorldCodeRecipeProvenance.enterPendingBodyFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {callerσ callerτ : Subst}
    {m : Nat} {selectedKey : Key m} {selectedResult selectedSupport : Profile m}
    {selectedRows : List (Key m × Profile m)}
    {parent : RichCodeRecipe env U registry target callerSource callerLocals callerσ.tail
      (.forallE callerA callerB) relevant
      (.pi prototypeDomain prototypeBody selectedSupport selectedRows) parentFootprint}
    (annotation : WorldCodeRecipeProvenance strata parent)
    (selected : (selectedKey, selectedResult) ∈ selectedRows)
    (anchorEq : selectedKey.anchor = callerσ 0)
    {callerContext : ContextDerivation callerEnv U (callerA :: callerSource)}
    (caller : EndpointState callerEnv U (callerA :: callerSource) callerB callerAssigned)
    (callerControls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U callerEnvironment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld callerControls .fundamental caller baseline])
    (sources : annotation.Sources P)
    (annotationPaid : Sponsored frontier annotation.worlds)
    (bounded : EquationStratifiedFuel.WithinAbove callerControls.cutoff callerControls.fuel
      (fun control => parent.stratifiedDepth (strata.headOrdinal registry) control))
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      (Locals.push callerLocals) callerσ callerτ callerAvailable)
    (callerSubstitutions : Ctx.SubstEq env U target callerσ callerτ (callerA :: callerSource))
    (callerResources : Footprint.Available ((0, Need.mk m selectedKey.input) ::
      parentFootprint.sourceLift (.skip .refl)) callerAvailable)
    (callerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld callerControls .fundamental caller baseline]))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (sourceBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sourcePaid : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {table : List (Key n × Profile n)}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      pending.oldKey pending.oldResult)
    (ready : row.Controlled controls frontier) :
    Nonempty (RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ (callerτ 0) hu hv captured) ∧
    TypeRelated env U registry target (callerB.subst callerσ) (callerB.subst callerτ) selectedResult := by
  have resources := callerFrame.recipeResources henv hscoped formed callerResources
  have previous : RecipeResourceRealization env U registry target callerSource callerσ.tail callerτ.tail parentFootprint := by
    intro index need member assigned lookup
    obtain ⟨value⟩ := resources (index + 1) need
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(index, need), member, rfl⟩))
      assigned.lift (.succ lookup)
    exact ⟨by simpa only [lift_subst, Subst.tail] using value⟩
  have tailSubstitutions : Ctx.SubstEq env U target callerσ.tail callerτ.tail callerSource := by
    cases callerSubstitutions with
    | cons tail _ _ => exact tail
  have calls := annotation.callsOfBank formed caller callerControls baseline frontier callerPaid
    sources annotationPaid callerBank
  obtain ⟨_, _, _, _, whole⟩ := annotation.rebuildWorld henv hscoped formed
    callerControls.cutoff callerControls.cutoffBound callerControls.fuel
    callerControls.ordered.constantCount
    (richSchedule .fundamental (Closure.close (caller.dependencyOrigin callerControls.ordered) callerEnvironment).cost)
    calls bounded tailSubstitutions previous
  obtain ⟨argument⟩ := resources 0 _ List.mem_cons_self callerA.lift (.zero (Γ := callerSource) (ty := callerA))
  have raw := callerSubstitutions.lookup (Lookup.zero (Γ := callerSource) (ty := callerA))
  have paired : Related env U registry target (callerσ 0) (callerτ 0) (callerA.subst callerσ.tail)
      selectedKey.input argument.support := by simpa only [lift_subst] using argument.related
  rw [lift_subst] at raw
  have admitted := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
    (by simpa only [subst] using whole) selected anchorEq raw paired
  have code := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
    (by simpa only [subst] using whole) selected anchorEq raw paired
  have leftEq : callerσ.tail.cons (callerσ 0) = callerσ := by funext i; cases i <;> rfl
  have rightEq : callerτ.tail.cons (callerτ 0) = callerτ := by funext i; cases i <;> rfl
  refine ⟨pending.enterBodyWorld initial henv hscoped sourceBelow controls domain domainLocation
    body bodyLocation bodyContext hu hv frame captured frontier data sourceBank sourcePaid closed formed
    substitutions row ready admitted, ?_⟩
  simpa only [inst_lift_cons, leftEq, rightEq] using code

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
