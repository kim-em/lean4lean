import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableValue
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableStep
import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem legacyTrace
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (trace : VariableTrace env U registry target index profile footprint)
    (resources : footprint.Available available)
    (leaf : ∀ {n} (demand : Profile n), Need.mk n demand ∈ available index →
      Nonempty (RichSupportedValue sourceEnv env U registry target owner locals σ τ available demand)) :
    Nonempty (RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile) := by
  induction trace with
  | leaf demand => exact leaf demand (resources _ _ List.mem_cons_self)
  | empty => exact ⟨.empty⟩
  | union first second ihl ihr =>
    obtain ⟨left⟩ := ihl (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨right⟩ := ihr (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨left.union henv right⟩
  | view source view ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.action henv hscoped formed (.view view)⟩
  | pad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.pad henv⟩
  | unpad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.unpad henv formed⟩
  | rowShift source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨(source.pad henv).action henv hscoped formed (.view (.commutePadFn _ _))⟩

private theorem richTrace
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (resources : footprint.Available available)
    (leaf : ∀ {n} (demand : Profile n), Need.mk n demand ∈ available index →
      Nonempty (RichSupportedValue sourceEnv env U registry target owner locals σ τ available demand)) :
    Nonempty (RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile) := by
  induction trace with
  | legacy source => exact legacyTrace henv hscoped formed source resources leaf
  | union first second ihl ihr =>
    obtain ⟨left⟩ := ihl (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨right⟩ := ihr (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨left.union henv right⟩
  | code source action sorted ih =>
    obtain ⟨source⟩ := ih resources
    exact source.code henv hscoped formed action sorted
  | action source action ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.action henv hscoped formed action⟩
  | pad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.pad henv⟩
  | unpad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨source.unpad henv formed⟩

/-- Full variable F step for the current rich grammar. Every comparison
query is selected from the actual stored domain certificate and comes with
a strict bound for the actual captured environment. All incoming wrappers
are replayed by finite source code/support actions. -/
theorem HeaderBinderFrame.variableStep
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {level : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (lookup : Lookup headerSource index sourceType) (levelWF : level.WF U)
    (formation : EndpointState headerEnv U headerSource sourceType (.sort level))
    (compare : ∀ {n} (demand : Profile n)
      (entry : MeasuredHeaderBinderEntry frame index (Need.mk n demand) sourceType),
      (Closure.close (entry.originalDomain.dependencyOrigin hf)
        (entry.tailFrame.dependencyEnvironment hf sf initial)).cost +
      (Closure.close (formation.dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost <
      (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost →
      RichCert headerEnv env U registry target (.ref entry.originalDomain)
        entry.tailLocals entry.tailLeft true entry.support entry.footprint →
      entry.footprint.Available entry.tailAvailable →
      Nonempty (RichCodeTransferResult env U registry target (.ref entry.originalDomain)
        formation locals entry.tailLeft left available true entry.support))
    (query : RichObs headerEnv env U registry target (.bvar lookup levelWF formation)
      locals left profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    Nonempty (RichSupportedValue headerEnv env U registry target
      (.bvar lookup levelWF formation) locals left right available profile) := by
  obtain ⟨_, ⟨source⟩, resources⟩ := query.variableQuery closed resources
  apply richTrace henv hscoped formed source.variableTrace resources
  intro n demand member
  obtain ⟨entry⟩ := frame.lookupMeasured henv formed member lookup
  obtain ⟨answer⟩ := compare demand entry (entry.comparison_bound hf sf initial lookup levelWF formation)
    entry.certificate entry.resources
  have code : TypeRelated env U registry target (sourceType.subst left)
      (sourceType.subst left) entry.support := by
    simpa only [entry.toHeaderBinderEntry.realizedType] using answer.related
  exact ⟨{
    support := entry.support
    footprint := answer.footprint
    certificate := answer.certificate
    resources := answer.resources
    typed := entry.typed
    related := Related.retag henv entry.typed code entry.related
    typeCode := code }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
