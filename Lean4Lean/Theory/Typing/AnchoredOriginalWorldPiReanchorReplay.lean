import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! The reanchor semantic step applies qualified unary induction to the exact
original domain and body, keeping controls on the same returned body query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem singletonSponsoredBelow
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    {child parent : World strata.rules.length}
    (sponsored : Sponsored frontier [parent])
    (lower : WorldBelow strata.rules.length child parent) :
    Sponsored frontier [child] := by
  intro value member
  cases List.mem_singleton.mp member
  obtain ⟨sponsor, member, bound⟩ := sponsored parent (List.mem_singleton_self _)
  exact ⟨sponsor, member, EquationWorldClosureOrder.trans
    (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans lower bound⟩

private theorem worldCode
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier parent : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P parent)
    (funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental node captured]) parent)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (provenance : EndpointProvenance context node)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ answer : RichCodeTransferResult env U registry target node node locals σ τ available relevant profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  obtain ⟨answer, _, ⟨answerReady⟩⟩ := (bank _ funded).computational node provenance controls frame captured captured
    frontier (Nat.le_refl _) (Covered.refl _) rfl sponsored data closed formed substitutions
    (.code certificate) resources {
      annotation := .code ready.annotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using ready.within control active
      sponsored := ready.sponsored }
  obtain ⟨outputFootprint, output, outputReady, outputResources, _⟩ :=
    answer.rightQuery.code_controlled henv controls answerReady certificate.formed
  exact ⟨⟨outputFootprint, output, outputResources,
    answer.related.code_of_sortable henv hscoped formed certificate.formed⟩, ⟨outputReady⟩⟩

/-- The actual binder extends the identity generation whose base is the
retained paired tail. Its atomized head table and old base ancestry are kept
before the proper body call. -/
theorem WorldUnaryFrameData.bind
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) {input : Profile n} (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (headClosed : Valuation.AtomClosed (fun _ : Nat => needs)) :
    Nonempty (WorldUnaryFrameData P controls frontier
      ((OriginalRichFrame.bind frame domain certificate resources typed arguments needs bounded covered).reserve
        [.close (domain.dependencyOrigin controls.ordered) (frame.dependencyEnvironment controls.ordered)])
      (reservedBindWorldEnvironment controls domain captured captured)) := by
  let tail := data.generation substitutions
  let generated := WorldGenerated.bind tail captured (Nat.le_refl _) domain A subst_id certificate resources typed arguments
    needs bounded covered
  obtain ⟨ready⟩ := WorldGenerated.Controlled.ofRetainedQueries generated (fun query member => by
    change query ∈ .certificate certificate :: frame.raw.storedQueries at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨certificateReady⟩
    · exact data.queries query member)
  let ancestry := data.generation_hereditary substitutions
  have hereditary : generated.Hereditary frontier :=
    ⟨⟨ancestry.tablesClosed, headClosed⟩, ancestry.bases, ancestry.ready⟩
  have replayable : generated.Replayable := ⟨trivial, Covered.refl _⟩
  have compatible : generated.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  exact WorldUnaryFrameData.ofGenerated
    ((OriginalRichFrame.bind frame domain certificate resources typed arguments needs bounded covered).reserve
      [.close (domain.dependencyOrigin controls.ordered) (frame.dependencyEnvironment controls.ordered)])
    generated ready replayable compatible hereditary

/-- Reanchor a real retained row through the two strictly smaller original
formation calls. The exact returned body certificate carries its controls. -/
theorem RichPiRowCertificate.reanchorWorld
    {anchor : VExpr} {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation headerEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (controls : OriginalWorldControls strata headerEnv)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initialContext =
      .cons (location.contextDerivation initialContext) domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame headerEnv env U registry target (location.contextDerivation initialContext)
      locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ output : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      (reanchorKey key anchor) result,
      Nonempty (output.Controlled controls frontier) := by
  have funding := piRowWorldFunding controls domain body hu hv captured frontier
  have children := piRowWorldChildren controls domain body hu hv captured
  obtain ⟨domainAnswer, _⟩ := worldCode controls frame captured frontier _ bank funding.1
    (singletonSponsoredBelow sponsored children.1) (.ofLocation location initialContext) data
    henv hscoped closed formed substitutions row.domain row.domainAvailable ready.domain
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, pair, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainAnswer.related pair
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
  obtain ⟨bodyData⟩ := data.bind substitutions domain row.domain row.domainAvailable
    row.inputTyped arguments needs bounded covered ready.domain
    (atomizedNeeds_closed row.bodyFootprint.localNeeds)
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: headerSource) :=
    .cons substitutions (domain.sound.defeq.mono headerBelow) raw
  have bodyProvenance : EndpointProvenance (.cons (location.contextDerivation initialContext) domain) body :=
    bodyContext ▸ EndpointProvenance.ofLocation bodyLocation initialContext
  obtain ⟨answer, ⟨answerReady⟩⟩ := worldCode controls bodyFrame bodyCaptured frontier _ bank funding.2
    (singletonSponsoredBelow sponsored children.2) bodyProvenance bodyData henv hscoped
    (Valuation.push_atomized_closed closed _) formed paired row.body
    (row.pack.available_atomized_localNeeds row.outsideAvailable) ready.body
  obtain ⟨packed, outside, pack, coverage, resources⟩ := Footprint.pack_available answer.resources bounded covered
  exact ⟨{ row with
    anchor := admitted.reset_anchor
    bodyFootprint := answer.footprint
    body := answer.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources }, ⟨⟨ready.domain, answerReady⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
