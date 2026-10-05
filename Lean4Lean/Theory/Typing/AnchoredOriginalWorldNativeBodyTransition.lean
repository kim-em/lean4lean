import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiProgramDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution

/-! Native Pi execution enters the selected original body and its exact
annotation. Prefix changes only retarget the real lower-call bank; output
operations stay in the ranked row continuation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem RichPiRowCertificate.enterOriginalBodyWorldExact
    {anchor : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (provenance : EndpointProvenance context (.pi hu hv (.ref domain) body))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body key result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv captured,
      execution.ready = ready.body := by
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, location, contextEq⟩
  cases contextEq
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial)
      (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  exact row.enterBodyWorldExact initial henv hscoped sourceBelow controls
    domain (.piDomain location) body (.piBody location) bodyContext hu hv frame captured frontier data
    bank paid closed formed substitutions ready admitted

private theorem prefixCalls
    {strata : EquationStratification env}
    {child parent : World strata.rules.length}
    (frontier : List (World strata.rules.length))
    (smaller : WorldBelow strata.rules.length child parent) :
    CallBelow strata.rules.length (frontier ++ [child]) (frontier ++ [parent]) := by
  induction frontier with
  | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact smaller)
  | cons world rest ih => exact ih.cons world

/-- This is the native Pi machine transition. The admission belongs to the
selected instruction; no row certificate, body answer or selected frame is
provided by the caller. All of those are computed from the literal leaf. -/
theorem enterSelectedNativeBodyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {nextAmbient : Profile m} {nextTable : List (Key m × Profile m)}
    {selectedKey : Key m} {selectedResult : Profile m}
    {domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domainCode)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv (.ref domain) body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domainCode guard rows resources).headDepth policy ≤
      incoming.headDepth policy)
    (budget : Nat)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody nextAmbient nextTable))
    (member : (selectedKey, selectedResult) ∈ nextTable)
    (admitted : Admitted env U registry target selectedKey anchor anchor) :
    ∃ pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body pending.oldKey pending.oldResult,
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv captured,
      HEq row.domain domainCode ∧
      sizeOf (show WorldCertProvenance strata row.body from execution.ready.annotation) < budget ∧
      execution.ready.annotation.worlds ⊆ ready.annotation.worlds ∧
      ∀ policy, row.body.headDepth policy ≤ incoming.headDepth policy := by
  let domainReady := WorldPiProgramLeafProvenance.nativeDomainReady
    domainAnnotation rowsAnnotation ready included depth
  have rowsBound : sizeOf rowsAnnotation ≤ budget := by
    simp only [WorldPiProgramLeafProvenance.retainedSize] at smaller
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_lt smaller)
  have rowsDepth : ∀ policy, rows.headDepth policy ≤ incoming.headDepth policy := by
    intro policy
    apply Nat.le_trans (Nat.le_max_right _ _)
    simpa only [RichPiProgramLeaf.headDepth] using depth policy
  have rowsWorlds : rowsAnnotation.worlds ⊆ ready.annotation.worlds := by
    intro world present
    apply included
    simpa only [WorldPiProgramLeafProvenance.worlds] using
      List.mem_append_right domainAnnotation.worlds present
  obtain ⟨pending, row, rowReady, sameDomain, _, bodyWorlds, bodyDepth, bodySize⟩ :=
    rowsAnnotation.pathNativeCursorSized domainCode budget rowsBound domainReady
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
      (fun control active => Nat.le_trans (rowsDepth _) (ready.within control active))
      (fun world member => ready.sponsored world (rowsWorlds member)) path member
  let piProvenance : EndpointProvenance context (.pi hu hv (.ref domain) body) := {
    provenance with
    location := route.locate provenance.location
    context_eq := provenance.context_eq.trans
      (route.locate_contextDerivation provenance.location provenance.initial).symm }
  have cost := route.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered)
  have parentRelation : originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured =
      originalCallWorld controls .fundamental node captured ∨
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured)
        (originalCallWorld controls .fundamental node captured) := by
    rcases Nat.eq_or_lt_of_le cost with same | smaller
    · left
      simp only [originalCallWorld, same]
    · exact .inr (original_child (richSchedule_strict smaller _ _) _ _ _ _ _)
  have piPaid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured] := by
    rcases parentRelation with same | smaller
    · simpa only [same] using paid
    · exact singletonSponsoredBelow paid smaller
  have piBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]) := by
    intro calls lower
    apply bank calls
    rcases parentRelation with same | smaller
    · simpa only [same] using lower
    · exact lower.trans (prefixCalls frontier smaller)
  obtain ⟨execution, sameReady⟩ := row.enterOriginalBodyWorldExact piProvenance frame captured data
    closed formed substitutions henv hscoped sourceBelow piPaid piBank rowReady
    (pending.oldAdmission henv hscoped formed row.anchor admitted)
  refine ⟨pending, row, execution, sameDomain, ?_, ?_, ?_⟩
  · simpa only [sameReady] using bodySize
  · rw [sameReady]
    intro world present
    exact rowsWorlds (bodyWorlds present)
  · exact fun policy => Nat.le_trans (bodyDepth policy) (rowsDepth policy)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
