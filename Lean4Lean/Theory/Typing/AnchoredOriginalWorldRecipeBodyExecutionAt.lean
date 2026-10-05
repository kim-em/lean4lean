import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorBaseline

/-! Enter the SAME selected Pi row beneath the immutable enclosing budget.
Actual capacity and world coverage admit the selected frame; only its proper
original domain and reserved body calls are retargeted to the fixed baseline. -/
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

theorem RichPiRowCertificate.enterBodyWorldAtExact
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
    {baselineEnvironment : List Closure}
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured,
      execution.ready = ready.body := by
  have children := piRowWorldChildren controls domain body hu hv captured
  have domainBelow := originalCallWorld_retargetBelow controls (.pi hu hv (.ref domain) body)
    .fundamental captured baseline capacity covered children.1
  have bodyBelow := originalCallWorld_retargetBelow controls (.pi hu hv (.ref domain) body)
    .fundamental captured baseline capacity covered children.2
  have fund {child : World strata.rules.length}
      (smaller : WorldBelow strata.rules.length child
        (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline)) :
      CallBelow strata.rules.length (frontier ++ [child])
        (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]) := by
    have step := split_call (calls := [child])
      (fun current member => by cases List.mem_singleton.mp member; exact smaller)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ [child])
          (sponsors ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  obtain ⟨domainAnswer, _⟩ := worldCode controls frame captured frontier _ bank (fund domainBelow)
    (singletonSponsoredBelow sponsored domainBelow) (.ofLocation domainLocation initial) data
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
    children.2, singletonSponsoredBelow sponsored bodyBelow, ?_⟩, rfl⟩
  intro retained lower
  exact bank retained (lower.trans (fund bodyBelow))

/-- Compatibility entry retaining the same actual body execution. -/
theorem RichPiRowCertificate.enterBodyWorldAt
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
    {baselineEnvironment : List Closure}
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured) := by
  obtain ⟨execution, _⟩ := row.enterBodyWorldAtExact initial henv hscoped sourceBelow controls domain domainLocation body bodyLocation
    bodyContext hu hv frame captured baseline capacity covered frontier data bank sponsored closed formed substitutions
    ready admitted
  exact ⟨execution⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
