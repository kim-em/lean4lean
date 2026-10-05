import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerHeaderTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHeaderFamilyPlan
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyResources
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderSinglePi

/-! Extract the exact demanded domain support from the genuine caller
header reply. The same paired request is converted to that declared domain;
neither a native row's smaller support nor a new semantic answer is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private oneDomain_eq from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem domainAtCast
    {node : EndpointState sourceEnv U source expression assigned}
    {domain : EndpointState sourceEnv U source C (.sort cu)}
    {body : EndpointState sourceEnv U (C :: source) D (.sort dv)}
    (declared : expression = .forallE C D)
    (certificate : RichCert sourceEnv env U registry target node locals realization relevant
      (Profile.pi prototypeDomain prototypeBody support rows) footprint)
    (hcu : cu.WF U) (hdv : dv.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE C D) (node.cast declared rfl)
      (.pi hcu hdv domain body))
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ result : RichDomainCertificate env U registry target domain locals realization available support,
      Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) := by
  cases declared
  obtain ⟨result, controlled, _, _⟩ := certificate.piDomain_controlled hcu hdv route resources ready
  exact ⟨result, ⟨controlled⟩⟩

/-- The certificate and admission retain exactly the input and support
of the incoming request, including assigned-sort and additional demands. -/
theorem AmbientBoundedParameterReply.headerDomainRequestWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (controls : OriginalWorldControls strata origin.source)
    (frontier : List (World strata.rules.length))
    {domain : EndpointRef origin.source U [] C (.sort cu)}
    {body : EndpointState origin.source U [C] D (.sort dv)}
    (declared : info.type.instL levels = .forallE C D)
    (hcu : cu.WF U) (hdv : dv.WF U)
    (route : PrefixRoute origin.source U [] (.forallE C D)
      ((EndpointState.ref (origin.familyHeader levelsWF).reference).cast declared rfl)
      (.pi hcu hdv (.ref domain) body))
    {input support : Profile n} {rows : List (Key n × Profile n)}
    (incoming : AmbientBoundedParameterReply base caps (.forallE A B)
      (RetainedHeaderUniverse.display origin levelsWF common) commonLeft commonRight
      (Profile.pi prototypeDomain prototypeBody support rows) (environmentCost ([] : List Closure)))
    (incomingData : WorldParameterReplyData (P := P) controls .nil frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi prototypeDomain prototypeBody support rows).HasType (.sort relevant))
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨A, leftValue, input⟩, support⟩ : DataRequest (Profile n)) leftValue rightValue) :
    ∃ result : RichDomainCertificate env U registry target (.ref domain) [] commonLeft (fun _ => []) support,
      Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨⟨C.subst commonLeft, leftValue, input⟩, support⟩ : DataRequest (Profile n)) leftValue rightValue := by
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    incoming.reply.answer.reply.query.code_controlled henv controls incomingData.query sorted
  have localsEq : incoming.reply.answer.reply.locals = [] := incoming.reply.answer.reply.locals_eq
  have availableEq : incoming.reply.answer.reply.available = (fun _ => []) :=
    incomingData.generation.emptyAvailable
  have extracted := domainAtCast declared certificate hcu hdv route resources certificateReady
  change ∃ result : RichDomainCertificate env U registry target (.ref domain)
      incoming.reply.answer.reply.locals commonLeft incoming.reply.answer.reply.available support,
    Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) at extracted
  rw [localsEq, availableEq] at extracted
  obtain ⟨result, resultReady⟩ := extracted
  have whole : TypeRelated env U registry target (.forallE A B)
      (.forallE (C.subst commonLeft) (D.subst commonLeft.lift))
      (Profile.pi prototypeDomain prototypeBody support rows) := by
    have whole := incoming.related
    change TypeRelated env U registry target (.forallE A B)
      ((info.type.instL levels).subst commonLeft) _ at whole
    rw [declared] at whole
    exact whole
  have bridge := TypeRelated.literalPiDomain henv hscoped formed whole
  have path := TypeRelated.literalPiDomainPath henv formed whole
  obtain ⟨anchor, pair, typed, formation, _domain, first, second⟩ := admission
  exact ⟨result, resultReady, path.cast anchor, path.cast pair, typed, formation,
    (bridge.symm henv typed.wf_type).left_diagonal,
    Related.convert henv typed bridge first, Related.convert henv typed bridge second⟩

/-- The genuine whole-header reply supplies the declared-domain evidence
used by the actual enriched plan. Its paired admission remains in the output. -/
theorem AmbientBoundedParameterReply.oneParameterHeaderPlanWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (controls : OriginalWorldControls strata origin.source)
    (frontier : List (World strata.rules.length))
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    {input support : Profile n} {rows : List (Key n × Profile n)}
    (incoming : AmbientBoundedParameterReply base caps (.forallE A B)
      (RetainedHeaderUniverse.display origin levelsWF common) commonLeft commonRight
      (Profile.pi prototypeDomain prototypeBody support rows) (environmentCost ([] : List Closure)))
    (incomingData : WorldParameterReplyData (P := P) controls .nil frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi prototypeDomain prototypeBody support rows).HasType (.sort relevant))
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨A, leftValue, input⟩, support⟩ : DataRequest (Profile n)) leftValue rightValue) :
    let request : DataRequest (Profile n) := ⟨⟨C.subst commonLeft, leftValue, input⟩, support⟩
    RankedData.RequestAdmission env U (relations env U registry n) target request leftValue rightValue ∧
    ∃ plan : RichFamilyPlanResult env U registry target (origin.familyHeader levelsWF).reference
        name levels signature .nil (.ref (origin.familyHeader levelsWF).reference) commonLeft [] (fun _ => [])
        (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, levels, familyRelevant, [request]⟩)),
      Nonempty (plan.WorldControlled controls frontier) := by
  let selected := origin.singlePiSyntax levelsWF signature domains
  obtain ⟨domainCode, ⟨domainReady⟩, paired⟩ := incoming.headerDomainRequestWorld origin levelsWF controls frontier
    (oneDomain_eq signature domains) selected.hcu selected.hdv selected.route incomingData henv hscoped formed sorted admission
  obtain ⟨plan, ⟨planReady⟩⟩ := OriginalRecordSource.oneParameterHeaderPlanWorld controls frontier
    (header := (origin.familyHeader levelsWF).reference) (signature := signature) (body := selected.body)
    henv selected.hcu selected.hdv domains resultSort relevance selected.location selected.lineage domainCode.certificate domainCode.resources domainReady paired
  obtain ⟨restored, restoredReady⟩ := plan.restoreSingleHeaderControlled domains selected.route planReady
  exact ⟨paired, restored, restoredReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
