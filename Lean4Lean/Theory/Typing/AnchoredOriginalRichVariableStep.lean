import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries

/-! The variable step compares two retained formation occurrences: the
stored domain displayed under the intervening binders, and the independently
retained formation child of the original variable. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def HeaderBinderEntry.domainDisplay
    {context : ContextDerivation headerEnv U headerSource}
    {frame : HeaderBinderFrame header field major env registry target context locals left right available}
    (entry : HeaderBinderEntry frame index need sourceType) :
    EndpointDisplay headerEnv U headerSource sourceType (.sort entry.level) where
  source := entry.tailSource
  sourceExpression := entry.domain
  sourceType := .sort entry.level
  context := entry.tailContext
  node := .ref entry.originalDomain
  provenance := ⟨_, _, _, header, .nil, entry.headerLocation, entry.headerLineage.symm⟩
  map := .skipN .refl (index + 1)
  insertion := by
    have h := Ctx.liftN_iff_lift'.mp (Ctx.LiftN.zero (Γ := entry.tailSource) (entry.front ++ [entry.domain]))
    simpa only [List.length_append, List.length_singleton, Lift.consN, List.append_assoc, List.singleton_append, ← entry.index_eq, ← entry.source_eq] using h
  expression_eq := by
    exact entry.sourceType_eq.trans (lift'_consN_skipN (k := 0)).symm
  type_eq := rfl

theorem HeaderBinderEntry.realizedType
    {frame : HeaderBinderFrame header field major env registry target context locals left right available}
    (entry : HeaderBinderEntry frame index need sourceType) :
    entry.domain.subst entry.tailLeft = sourceType.subst left := by
  rw [← entry.left_eq, ← subst_lift']
  exact congrArg (VExpr.subst · left) ((lift'_consN_skipN (k := 0)).trans entry.sourceType_eq.symm)

theorem HeaderBinderEntry.comparison_bound
    {context : ContextDerivation headerEnv U headerSource}
    {frame : HeaderBinderFrame header field major env registry target context locals left right available}
    {level : VLevel}
    (entry : HeaderBinderEntry frame index need sourceType)
    (headerOrdered : headerEnv.Ordered)
    (lookup : Lookup headerSource index sourceType) (levelWF : level.WF U)
    (formation : EndpointState headerEnv U headerSource sourceType (.sort level)) :
    (Closure.close (entry.originalDomain.dependencyOrigin headerOrdered)
      (entry.tailContext.dependencyClosures headerOrdered)).cost +
    (Closure.close (formation.dependencyOrigin headerOrdered)
      (context.dependencyClosures headerOrdered)).cost <
    (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin headerOrdered)
      (context.dependencyClosures headerOrdered)).cost := by
  have bound := environment_entry (entry.originalLocation.dependency_captured_member headerOrdered)
  simp only [EndpointState.dependencyOrigin, Closure.cost, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_mul, Nat.one_mul] at *
  omega

/-- One actual leaf invokes comparison only at its stored ORIGINAL domain
and the variable's ORIGINAL formation child. The incoming source certificate
remains under its exact tail realization; it is never relabelled by raw equality. -/
theorem HeaderBinderEntry.variableStep
    {context : ContextDerivation headerEnv U headerSource}
    {frame : HeaderBinderFrame header field major env registry target context locals left right available}
    {level : VLevel}
    (entry : HeaderBinderEntry frame index (Need.mk n demand) sourceType)
    (henv : env.Ordered)
    (lookup : Lookup headerSource index sourceType) (levelWF : level.WF U)
    (formation : EndpointState headerEnv U headerSource sourceType (.sort level))
    (comparison : RichCodeTransferResult env U registry target (.ref entry.originalDomain)
      formation locals entry.tailLeft left available true entry.support) :
    Nonempty (RichBinderValue headerEnv env U registry target
      (.bvar lookup levelWF formation) locals left right available demand) := by
  have code : TypeRelated env U registry target (sourceType.subst left)
      (sourceType.subst left) entry.support := by
    simpa only [entry.realizedType] using comparison.related
  exact ⟨{
    support := entry.support
    footprint := comparison.footprint
    certificate := comparison.certificate
    resources := comparison.resources
    typed := entry.typed
    related := Related.retag henv entry.typed code entry.related }⟩

/-- The rich step uses the actual captured owners and fresh binders, not
only the raw context formation spine. -/
theorem MeasuredHeaderBinderEntry.comparison_bound
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {frame : HeaderBinderFrame header field major env registry target context locals left right available}
    {level : VLevel}
    (entry : MeasuredHeaderBinderEntry frame index need sourceType)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (lookup : Lookup headerSource index sourceType) (levelWF : level.WF U)
    (formation : EndpointState headerEnv U headerSource sourceType (.sort level)) :
    (Closure.close (entry.originalDomain.dependencyOrigin hf)
      (entry.tailFrame.dependencyEnvironment hf sf initial)).cost +
    (Closure.close (formation.dependencyOrigin hf)
      (frame.dependencyEnvironment hf sf initial)).cost <
    (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin hf)
      (frame.dependencyEnvironment hf sf initial)).cost := by
  have bound := entry.environment_le hf sf initial
  simp only [EndpointState.dependencyOrigin, Closure.cost, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_mul, Nat.one_mul] at *
  omega

/-- A concrete leaf of the induction step: lookup chooses the exact original
query; the induction continuation is called with its computed strict bound,
its unmodified rich certificate, and its actual preceding-frame resources. -/
theorem HeaderBinderFrame.variableLeafStep
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {level : VLevel}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (member : Need.mk n demand ∈ available index)
    (lookup : Lookup headerSource index sourceType) (levelWF : level.WF U)
    (formation : EndpointState headerEnv U headerSource sourceType (.sort level))
    (compare : ∀ entry : MeasuredHeaderBinderEntry frame index (Need.mk n demand) sourceType,
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
        formation locals entry.tailLeft left available true entry.support)) :
    Nonempty (RichBinderValue headerEnv env U registry target
      (.bvar lookup levelWF formation) locals left right available demand) := by
  obtain ⟨entry⟩ := frame.lookupMeasured henv formed member lookup
  obtain ⟨answer⟩ := compare entry (entry.comparison_bound hf sf initial lookup levelWF formation)
    entry.certificate entry.resources
  exact entry.toHeaderBinderEntry.variableStep henv lookup levelWF formation answer

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
