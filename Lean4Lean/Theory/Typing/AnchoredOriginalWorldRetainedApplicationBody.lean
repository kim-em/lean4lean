import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode

/-! The entered `.body` state selects the literal retained application
program. Physical operands are executed immediately by the proper original
child calls; charged operands retain their exact unsynthesized recipe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- An explicit residual is distinct from an executed physical leaf. Its
index retains the original recipe, profile and atom selection. -/
inductive RetainedApplicationStep
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length)) (τ : Subst) (available : Valuation) :
    RetainedApplicationOrigin root env registry target source locals σ f a → Type where
  | executed {actual : RichAppOrigin root env registry target source locals σ f a}
      (answer : RetainedApplicationAnswers actual controls frontier τ available) :
      RetainedApplicationStep controls frontier τ available (.original actual)
  | pending (actual : RetainedChargedAppOrigin root env registry target source locals σ f a) :
      RetainedApplicationStep controls frontier τ available (.charged actual)

/-- Joint selected-program execution. The only semantic calls are the two
proper original operand Fs in the physical alternative. -/
theorem ControlledStoredQuery.executeRetainedApplication
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (selected : atom ∈ profile.atoms) :
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ ready.annotation.worlds ∧
      origin.RootedAt node ∧ (∀ policy, origin.headDepth policy ≤ query.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available origin) := by
  obtain ⟨origin, children, path, included, worlds, rooted, depth⟩ :=
    ready.annotation.retainedApplicationOrigin provenance.location selected
  have supplied : origin.footprint.Available
      available :=
    fun index need member => resources index need (included member)
  refine ⟨origin, children, path, supplied, worlds, rooted, depth, ?_⟩
  cases origin with
  | charged actual => exact ⟨.pending actual⟩
  | original actual =>
    cases children with
    | original annotation =>
      obtain ⟨route⟩ := rooted
      have functionReady : ControlledStoredQuery controls frontier (.observation actual.function) := {
        annotation := annotation.function
        within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_left _ member)) }
      have argumentReady : ControlledStoredQuery controls frontier (.observation actual.argument) := {
        annotation := annotation.argument
        within := fun control active => Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_right _ member)) }
      obtain ⟨answer⟩ := actual.executeWorld route provenance controls frame captured
        frontier data closed formed substitutions supplied
        functionReady argumentReady henv hscoped sourceBelow paid bank
      exact ⟨.executed answer⟩


/-- Actual body execution provides every frame, resource, and bank premise.
Only the selected requested atom is chosen by the consumer. -/
theorem RichPiRowBodyExecution.selectApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source D (.sort u)}
    {body : EndpointState sourceEnv U (D :: source) (.app f a) (.sort v)}
    {row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body key result}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv parentEnvironment)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ result.atoms) :
    ∃ origin : RetainedApplicationOrigin execution.provenance.root env registry target
        (D :: source) (Locals.push locals) (σ.cons key.anchor) f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) ∧
      children.worlds ⊆ execution.ready.annotation.worlds ∧
      origin.RootedAt body ∧ (∀ policy, origin.headDepth policy ≤ row.body.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier (τ.cons anchor)
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) origin) := by
  exact execution.ready.executeRetainedApplication execution.provenance execution.frame execution.captured
    execution.data execution.closed formed execution.substitutions execution.resources henv hscoped sourceBelow
    execution.sponsored execution.bank selected

/-- The `.domain` continuation at a literal native Pi enters its original
domain program and executes the selected application operands. No rebuilt
`.domain parent` recipe is used as recursive input. -/
theorem executeNativeDomainApplication
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (domain : EndpointRef sourceEnv U source (.app f a) (.sort u))
    (body : EndpointState sourceEnv U ((.app f a) :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domainCode))
    (provenance : EndpointProvenance context (.pi hu hv (.ref domain) body))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : domainFootprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (selected : atom ∈ ambient.atoms) :
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ domainReady.annotation.worlds ∧
      origin.RootedAt (.ref domain) ∧ (∀ policy, origin.headDepth policy ≤ domainCode.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available origin) := by
  have funding := piRowWorldFunding controls domain body hu hv captured frontier
  have children := piRowWorldChildren controls domain body hu hv captured
  let domainProvenance : EndpointProvenance context (.ref domain) := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .piDomain provenance.location, context_eq := provenance.context_eq }
  have lowerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref domain) captured]) :=
    fun retained smaller => bank retained (smaller.trans funding.1)
  obtain ⟨origin, annotations, path, supplied, worlds, rooted, depth, step⟩ :=
    domainReady.executeRetainedApplication domainProvenance frame captured data closed formed substitutions
      resources
      henv hscoped sourceBelow (singletonSponsoredBelow paid children.1) lowerBank selected
  exact ⟨origin, annotations, path, supplied, worlds, rooted, depth, step⟩

/-- Execute every retained output operation on the SAME selected ordinary
application certificate, then reattach its actual original conversion prefix. -/
theorem RetainedApplicationAnswers.codeAtOutputWorld
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RichAppOrigin root env registry target source locals σ f a}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (answer : RetainedApplicationAnswers origin controls frontier τ available)
    (route : PrefixRoute sourceEnv U source (.app f a) node origin.node)
    (path : GeneralOutputPath env U registry target origin.output output)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node
        locals τ relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available ∧
      ready.annotation.worlds ⊆ answer.functionQuery.annotation.worlds ++ answer.argumentQuery.annotation.worlds ∧
      TypeRelated env U registry target ((.app f a : VExpr).subst σ)
        ((.app f a : VExpr).subst τ) (.singleton output) := by
  obtain ⟨flag, originalSorted, ⟨change⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  obtain ⟨footprint, certificate, ready, resources, included, related⟩ :=
    answer.codeWorld henv hscoped formed closed originalSorted
  obtain ⟨nextFootprint, next, annotation, supplied, worlds, depth⟩ :=
    certificate.codeAction_worlds_depth ready.annotation change resources
  let result := RichCert.route route next
  let resultReady : ControlledStoredQuery controls frontier (.certificate result) := {
    annotation := .route route annotation
    within := by
      intro control active
      simpa only [result, StoredOriginalQuery.headDepth, RichCert.headDepth] using
        Nat.le_trans (depth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
          (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  exact ⟨nextFootprint, result, resultReady, supplied,
    fun world member => included (worlds member), change.codeMap henv hscoped related⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
