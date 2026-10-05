import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries
import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace

/-! Paired variable interpretation uses the exact stored domain occurrence,
its retained generic frame, and the original variable formation child. The
right observer is reconstructed from the actual available variable leaves.
No domain certificate is relabelled using equality of raw source types. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def OriginalRichEntry.domainDisplay
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType) :
    EndpointDisplay sourceEnv U source sourceType (.sort entry.level) where
  source := entry.tailSource
  sourceExpression := entry.domain
  sourceType := .sort entry.level
  context := entry.tailContext
  node := .ref entry.originalDomain
  provenance := ⟨_, _, _, entry.originalDomain, entry.tailContext, .here, rfl⟩
  map := .skipN .refl (index + 1)
  insertion := by
    have h := Ctx.liftN_iff_lift'.mp (Ctx.LiftN.zero (Γ := entry.tailSource) (entry.front ++ [entry.domain]))
    simpa only [List.length_append, List.length_singleton, Lift.consN, List.append_assoc,
      List.singleton_append, ← entry.index_eq, ← entry.source_eq] using h
  expression_eq := entry.sourceType_eq.trans (lift'_consN_skipN (k := 0)).symm
  type_eq := rfl

theorem OriginalRichEntry.realizedType
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType) :
    entry.domain.subst entry.tailLeft = sourceType.subst left := by
  rw [← entry.left_eq, ← subst_lift']
  exact congrArg (VExpr.subst · left) ((lift'_consN_skipN (k := 0)).trans entry.sourceType_eq.symm)

theorem OriginalRichEntry.comparison_bound
    {level : VLevel}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    (ordered : sourceEnv.Ordered)
    (lookup : Lookup source index sourceType) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source sourceType (.sort level)) :
    (Closure.close (entry.originalDomain.dependencyOrigin ordered)
      (entry.tailFrame.dependencyEnvironment ordered)).cost +
    (Closure.close (formation.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost <
    (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost := by
  have bound := entry.environment_le ordered
  simp only [EndpointState.dependencyOrigin, Closure.cost, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_mul, Nat.one_mul] at *
  omega

private theorem legacyTrace
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (trace : VariableTrace env U registry target index profile footprint)
    (resources : footprint.Available available)
    (leaf : ∀ {n} (demand : Profile n), Need.mk n demand ∈ available index →
      Nonempty (RichComputationalValue sourceEnv env U registry target owner locals σ τ available demand)) :
    Nonempty (RichComputationalValue sourceEnv env U registry target owner locals σ τ available profile) := by
  induction trace with
  | leaf demand => exact leaf demand (resources _ _ List.mem_cons_self)
  | empty => exact ⟨.empty⟩
  | union first second ihl ihr =>
    obtain ⟨left⟩ := ihl (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨right⟩ := ihr (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨left.union henv hscoped formed right⟩
  | view source view ih =>
    obtain ⟨source⟩ := ih resources
    obtain ⟨right⟩ := source.rightQuery.action henv hscoped formed (.view view)
    exact ⟨{ source.toRichSupportedValue.action henv hscoped formed (.view view) with rightQuery := right }⟩
  | pad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨{ source.toRichSupportedValue.pad henv with rightQuery := source.rightQuery.pad henv hscoped formed }⟩
  | unpad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨{ source.toRichSupportedValue.unpad henv formed with rightQuery := source.rightQuery.unpad }⟩
  | rowShift source ih =>
    obtain ⟨source⟩ := ih resources
    obtain ⟨right⟩ := (source.rightQuery.pad henv hscoped formed).action henv hscoped formed
      (.view (.commutePadFn _ _))
    exact ⟨{ (source.toRichSupportedValue.pad henv).action henv hscoped formed
      (.view (.commutePadFn _ _)) with rightQuery := right }⟩

private theorem richTrace
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (resources : footprint.Available available)
    (leaf : ∀ {n} (demand : Profile n), Need.mk n demand ∈ available index →
      Nonempty (RichComputationalValue sourceEnv env U registry target owner locals σ τ available demand)) :
    Nonempty (RichComputationalValue sourceEnv env U registry target owner locals σ τ available profile) := by
  induction trace with
  | legacy source => exact legacyTrace henv hscoped formed source resources leaf
  | union first second ihl ihr =>
    obtain ⟨left⟩ := ihl (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨right⟩ := ihr (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨left.union henv hscoped formed right⟩
  | code source action sorted ih =>
    obtain ⟨source⟩ := ih resources
    obtain ⟨value⟩ := source.toRichSupportedValue.code henv hscoped formed action sorted
    exact ⟨{ value with rightQuery := source.rightQuery.codeAdapter henv hscoped formed action sorted }⟩
  | action source action ih =>
    obtain ⟨source⟩ := ih resources
    obtain ⟨right⟩ := source.rightQuery.action henv hscoped formed action
    exact ⟨{ source.toRichSupportedValue.action henv hscoped formed action with rightQuery := right }⟩
  | pad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨{ source.toRichSupportedValue.pad henv with rightQuery := source.rightQuery.pad henv hscoped formed }⟩
  | unpad source ih =>
    obtain ⟨source⟩ := ih resources
    exact ⟨{ source.toRichSupportedValue.unpad henv formed with rightQuery := source.rightQuery.unpad }⟩

/-- The R requests are exactly the entries selected by the available source
leaves. Both captured environments and the destination original formation
location are retained; the strict comparison bound is constructed here. -/
theorem OriginalRichFrame.variableComputational
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {level : VLevel}
    (lookup : Lookup source index sourceType) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source sourceType (.sort level))
    (location : Located root (.bvar lookup levelWF formation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initialContext) locals left right available)
    (compare : ∀ {n} (demand : Profile n)
      (entry : OriginalRichEntry frame index (Need.mk n demand) sourceType),
      richSchedule .expressionReindex
        ((Closure.close (entry.originalDomain.dependencyOrigin ordered)
          (entry.tailFrame.dependencyEnvironment ordered)).cost +
        (Closure.close (formation.dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost →
      RichCert sourceEnv env U registry target (.ref entry.originalDomain)
        entry.tailLocals entry.tailLeft true entry.support entry.footprint →
      entry.footprint.Available entry.tailAvailable →
      Nonempty (RichCodeTransferResult env U registry target (.ref entry.originalDomain)
        formation locals entry.tailLeft left available true entry.support))
    (query : RichObs sourceEnv env U registry target (.bvar lookup levelWF formation)
      locals left profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target
      (.bvar lookup levelWF formation) locals left right available profile) := by
  obtain ⟨_, ⟨source⟩, resources⟩ := query.variableQuery closed resources
  apply richTrace henv hscoped formed source.variableTrace resources
  intro n demand member
  obtain ⟨entry, _depth⟩ := frame.lookup_allDepth henv formed member lookup
  obtain ⟨answer⟩ := compare demand entry
    (richSchedule_strict (entry.comparison_bound ordered lookup levelWF formation) _ _)
    entry.certificate entry.resources
  have code : TypeRelated env U registry target (sourceType.subst left)
      (sourceType.subst left) entry.support := by
    simpa only [entry.realizedType] using answer.related
  have related := Related.retag henv entry.typed code entry.related
  exact ⟨{
    support := entry.support, footprint := answer.footprint
    certificate := answer.certificate, resources := answer.resources
    typed := entry.typed, related := related, typeCode := code
    rightQuery := {
      rank := n, bound := Nat.le_refl _, raw := demand
      footprint := [(index, Need.mk n demand)]
      observation := .legacy (.legacy (.var locals right index demand))
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := by
        intro i need hm
        cases List.mem_singleton.mp hm
        exact member
      live := related.live henv hscoped formed } }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
