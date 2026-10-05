import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationProgress

/-! Ranked pending row actions select an atom of the literal original body.
The actual body frame and the operand calls are unchanged by rank shifts,
reanchoring, input changes, or output support transformations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem RichPiRowBodyExecution.selectRankedApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source D (.sort u)}
    {body : EndpointState sourceEnv U (D :: source) (.app f a) (.sort v)}
    {table : List (Key n × Profile n)}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    {row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body pending.oldKey pending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv parentEnvironment)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ selectedResult.atoms) :
    ∃ origin : RetainedApplicationOrigin execution.provenance.root env registry target
        (D :: source) (Locals.push locals) (σ.cons pending.oldKey.anchor) f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) ∧
      children.worlds ⊆ execution.ready.annotation.worlds ∧
      origin.RootedAt body ∧ (∀ policy, origin.headDepth policy ≤ row.body.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier (τ.cons anchor)
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) origin) := by
  obtain ⟨oldAtom, oldMember, ⟨action⟩⟩ := pending.output.atom selected
  obtain ⟨origin, children, ⟨path⟩, resources, worlds, rooted, depth, step⟩ :=
    execution.selectApplicationWorld henv hscoped sourceBelow formed oldMember
  exact ⟨origin, children, ⟨.code path action (row.body.formed.singleton_of_mem oldMember)⟩,
    resources, worlds, rooted, depth, step⟩

/-- Pending row output operations preserve strict descent of the SAME retained
body annotation selected before entering its actual binder frame. -/
theorem RichPiRowBodyExecution.selectRankedApplicationWorldSized
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source D (.sort u)}
    {body : EndpointState sourceEnv U (D :: source) (.app f a) (.sort v)}
    {table : List (Key n × Profile n)}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    {row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body pending.oldKey pending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv parentEnvironment)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (selected : atom ∈ selectedResult.atoms) :
    ∃ origin : RetainedApplicationOrigin execution.provenance.root env registry target
        (D :: source) (Locals.push locals) (σ.cons pending.oldKey.anchor) f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) ∧
      children.worlds ⊆ execution.ready.annotation.worlds ∧
      origin.RootedAt body ∧
      children.retainedSize < sizeOf (show WorldCertProvenance strata row.body from execution.ready.annotation) ∧
      (∀ policy, origin.headDepth policy ≤ row.body.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier (τ.cons anchor)
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) origin) := by
  obtain ⟨oldAtom, oldMember, ⟨action⟩⟩ := pending.output.atom selected
  obtain ⟨origin, children, ⟨path⟩, resources, worlds, rooted, smaller, depth, step⟩ :=
    execution.ready.executeRetainedApplicationSized execution.provenance execution.frame execution.captured
      execution.data execution.closed formed execution.substitutions execution.resources henv hscoped sourceBelow
      execution.sponsored execution.bank oldMember
  exact ⟨origin, children, ⟨.code path action (row.body.formed.singleton_of_mem oldMember)⟩,
    resources, worlds, rooted, smaller, depth, step⟩

/-- The admission stored in an actual `fixedBody` instruction is sufficient
to enter the retained native body; no caller-variable resource or completed
body F answer is needed. The private source binder remains explicit in the
returned execution, so this theorem does not erase its operand resources. -/
theorem RankedPendingNativeRow.executeFixedApplicationWorld
    {anchor f a : VExpr} {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (domainLocation : Located root (.ref domain))
    (body : EndpointState sourceEnv U (A :: source) (VExpr.app f a).lift (.sort v))
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
    {table : List (Key n × Profile n)}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      pending.oldKey pending.oldResult)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target selectedKey anchor anchor)
    (selected : atom ∈ selectedResult.atoms) :
    ∃ execution : RichPiRowBodyExecution (P := P)
      (context := domainLocation.contextDerivation initial) controls frontier domain body row τ anchor hu hv captured,
    ∃ origin : RetainedApplicationOrigin execution.provenance.root env registry target
        (A :: source) (Locals.push locals) (σ.cons pending.oldKey.anchor) f.lift a.lift,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) ∧
      children.worlds ⊆ execution.ready.annotation.worlds ∧
      origin.RootedAt body ∧ (∀ policy, origin.headDepth policy ≤ row.body.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier (τ.cons anchor)
        (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) origin) := by
  obtain ⟨execution⟩ := pending.enterBodyWorld initial henv hscoped sourceBelow controls
    domain domainLocation body bodyLocation bodyContext hu hv frame captured frontier data bank sponsored
    closed formed substitutions row ready admitted
  obtain ⟨origin, children, path, resources, worlds, rooted, depth, step⟩ :=
    execution.selectRankedApplicationWorld pending henv hscoped sourceBelow formed selected
  exact ⟨execution, origin, children, path, resources, worlds, rooted, depth, step⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
