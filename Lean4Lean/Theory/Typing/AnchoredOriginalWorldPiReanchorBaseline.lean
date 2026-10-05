import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation

/-! Actual reanchoring at a selected frame is paid by the original fixed
Pi baseline. Both numerical capacity and hereditary world coverage are used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
open private worldCode singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem RichPiRowCertificate.reanchorWorldAt
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
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (ready : row.Controlled controls frontier)
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ output : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      (reanchorKey key anchor) result,
      Nonempty (output.Controlled controls frontier) := by
  have originalChildren := piRowWorldChildren controls domain body hu hv captured
  have domainBelow := originalCallWorld_retargetBelow controls (.pi hu hv (.ref domain) body)
    .fundamental captured baseline capacity covered originalChildren.1
  have bodyBelow := originalCallWorld_retargetBelow controls (.pi hu hv (.ref domain) body)
    .fundamental captured baseline capacity covered originalChildren.2
  have first : CallBelow strata.rules.length
      [originalCallWorld controls .fundamental (.ref domain) captured]
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline] :=
    split_call (fun child member => by cases List.mem_singleton.mp member; exact domainBelow)
  have second : CallBelow strata.rules.length
      [originalCallWorld controls .fundamental body (reservedBindWorldEnvironment controls domain captured captured)]
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline] :=
    split_call (fun child member => by cases List.mem_singleton.mp member; exact bodyBelow)
  have funding : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref domain) captured])
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]) ∧
      CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental body
        (reservedBindWorldEnvironment controls domain captured captured)])
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]) := by
    clear data bank sponsored ready
    induction frontier with
    | nil => exact ⟨first, second⟩
    | cons sponsor rest ih => exact ⟨ih.1.cons sponsor, ih.2.cons sponsor⟩
  obtain ⟨domainAnswer, _⟩ := worldCode controls frame captured frontier _ bank funding.1
    (singletonSponsoredBelow sponsored domainBelow) (.ofLocation location initialContext) data
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
    (singletonSponsoredBelow sponsored bodyBelow) bodyProvenance bodyData henv hscoped
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
