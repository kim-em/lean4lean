import Lean4Lean.Theory.Typing.AnchoredOriginalRichFullLookup

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private richTrace from Lean4Lean.Theory.Typing.AnchoredOriginalGenericVariable
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.variableComputationalFull
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
      entry.tailAvailable.AtomClosed →
      (∀ i, entry.tailAvailable i = available (i + (index + 1))) →
      pushedLocals (index + 1) entry.tailLocals = locals →
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
  obtain ⟨entry, tailClosed, fullAvailable, positions⟩ := frame.lookupFull henv formed closed member lookup
  obtain ⟨answer⟩ := compare demand entry tailClosed fullAvailable positions
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
