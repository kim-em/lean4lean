import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiQueryReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Full Pi query traversal with query-selected capped destination frames.
Each wrapper preserves the returned frame; union combines independent replies
at their fixed pre-answer capacity. Native cases retain actual original rows. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common destinationExpression destinationAssigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (empty : ∀ {n : Nat}, BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.empty : Profile n) capacity)
    (primitive : ∀ {n : Nat} {ambient : Profile n} {relevant : Bool}
      {prototypeDomain prototypeBody : VExpr} {table : List (Key n × Profile n)}
      {domainFootprint rowFootprint : Footprint},
      RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint →
      PiGuard env U target σ A B prototypeDomain prototypeBody →
      RichRows sourceEnv env U registry target domain body locals σ relevant ambient table rowFootprint →
      domainFootprint.Available available → rowFootprint.Available available →
      Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight
        (Profile.pi prototypeDomain prototypeBody ambient table) capacity))
include henv hscoped formed empty primitive

mutual
theorem _root_.Lean4Lean.AnchoredSource.Adapted.Obs.replayCappedPi
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match observation with
  | .empty => exact ⟨empty⟩
  | .pi domainCode guard rows =>
    exact primitive (.legacy (.ofCode domainCode domainCode.formed)) guard (rows.atOriginalPi domain body)
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.unpad⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact answer.action henv hscoped formed (.view view)
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact (answer.pad henv hscoped formed).action henv hscoped formed (.view (.commutePadFn key output))
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.CodeCert.replayCappedPi
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match certificate with
  | .seed source _ => exact source.replayCappedPi resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.unpad⟩
  | .familyPad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed .familyPad source.formed⟩
  | .down source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed .down source.formed⟩
  | .map view source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.map view) source.formed⟩
  | .select source member =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.select member) source.formed⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.focusMinimal minimal bound) source.formed⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.replayCappedPi
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match observation with
  | .legacy source => exact source.replayCappedPi resources
  | .code _ source => exact source.replayCappedPi resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.unpad⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact answer.action henv hscoped formed (.view view)
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact (answer.pad henv hscoped formed).action henv hscoped formed (.view (.commutePadFn key output))
  | .action source action =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact answer.action henv hscoped formed action
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.replayCappedPi
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match certificate with
  | .pi domainCode guard rows =>
    exact primitive (.legacy domainCode) guard (rows.atOriginalPi domain body)
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .ofCode source _ => exact source.replayCappedPi resources
  | .observe source _ => exact source.replayCappedPi resources
  | .seed source _ => exact source.replayCappedPi resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.unpad⟩
  | .familyPad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed .familyPad source.formed⟩
  | .down source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed .down source.formed⟩
  | .map view source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.map view) source.formed⟩
  | .select source member =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.select member) source.formed⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.focusMinimal minimal bound) source.formed⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed .sortPad source.formed⟩
  | .support action source =>
    obtain ⟨answer⟩ := source.replayCappedPi resources
    exact ⟨answer.codeAdapter henv hscoped formed (.support action) source.formed⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

private theorem replayCappedNativePiAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualBody : EndpointState sourceEnv U (A :: source) B (.sort actualV)}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B)
      (.pi actualHu actualHv actualDomain actualBody) (.pi hu hv domain body))
    (domainCode : RichCert sourceEnv env U registry target actualDomain locals σ true ambient domainFootprint)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows sourceEnv env U registry target actualDomain actualBody locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight
      (Profile.pi prototypeDomain prototypeBody ambient table) capacity) := by
  have equal := (PrefixRoute.done (.pi actualHu actualHv actualDomain actualBody)).structural_unique
    (by trivial) route (by trivial)
  obtain ⟨_, _, _, _, huEq, _, hvEq, domainEq, bodyEq⟩ :=
    EndpointState.pi.hinj rfl rfl rfl rfl equal.1 equal.2
  cases huEq
  cases hvEq
  have domainEq := eq_of_heq domainEq
  have bodyEq := eq_of_heq bodyEq
  cases domainEq
  cases bodyEq
  exact primitive domainCode guard rows domainAvailable resources

mutual
theorem RichCert.replayCappedPi
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body))
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match certificate with
  | .legacy source => exact source.replayCappedPi henv hscoped formed empty primitive resources
  | .observe source _ => exact source.replayCappedPi hu hv route resources
  | .pi actualHu actualHv domainCode guard rows =>
    exact replayCappedNativePiAt henv hscoped formed empty primitive actualHu actualHv hu hv route domainCode guard rows
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.replayCappedPi hu hv suffix resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi hu hv route (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi hu hv route (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .down source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.codeAdapter henv hscoped formed .down source.formed⟩
  | .map view source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.codeAdapter henv hscoped formed (.map view) source.formed⟩
  | .support action source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.codeAdapter henv hscoped formed (.support action) source.formed⟩
  | .select source member =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.codeAdapter henv hscoped formed (.select member) source.formed⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.replayCappedPi
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body))
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  match observation with
  | .legacy source => exact source.replayCappedPi henv hscoped formed empty primitive resources
  | .code source => exact source.replayCappedPi hu hv route resources
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.replayCappedPi hu hv suffix resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayCappedPi hu hv route (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayCappedPi hu hv route (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.unpad⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact answer.action henv hscoped formed (.view view)
  | .action source action =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact answer.action henv hscoped formed action
  | .select source member =>
    obtain ⟨answer⟩ := source.replayCappedPi hu hv route resources
    exact ⟨answer.restrict (fun atom present => (List.mem_singleton.mp present) ▸ member)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

end
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
