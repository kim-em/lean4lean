import Lean4Lean.Theory.Typing.AnchoredOriginalGenericVariableFull
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichEntry.tailSubstitutions
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    (substitutions : Ctx.SubstEq env U target left right source) :
    Ctx.SubstEq env U target entry.tailLeft entry.tailRight entry.tailSource := by
  have h : Ctx.SubstEq env U target left right ((entry.front ++ [entry.domain]) ++ entry.tailSource) := by
    simpa only [List.append_assoc, List.singleton_append] using entry.source_eq ▸ substitutions
  have h := Lean4Lean.AnchoredSource.Adapted.Ctx.SubstEq.nativePrefix h
  simpa only [List.length_append, List.length_singleton, ← entry.index_eq,
    entry.left_eq, entry.right_eq] using h

theorem OriginalRichEntry.liftedResources
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    {required : Footprint} (resources : required.Available entry.tailAvailable) :
    (required.sourceLift entry.domainDisplay.map).Available available := by
  intro i wanted member
  obtain ⟨⟨j, request⟩, before, equal⟩ := List.mem_map.mp member
  cases equal
  simpa only [OriginalRichEntry.domainDisplay, Lift.liftVar_skipN, Lift.liftVar] using
    entry.available_le j wanted (resources j wanted before)

/-- The suffix-to-full variable edge is an ordinary source lift. Its
reconstruction IH is queried at the actual original domain occurrence; the
identity destination freezes the chosen answer back to the original table.
The separate smaller unary original F supplies semantics, not a new oracle. -/
theorem OriginalRichEntry.freezeComparison
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {level : VLevel}
    (lookup : Lookup source index sourceType) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source sourceType (.sort level))
    (location : Located root (.bvar lookup levelWF formation))
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initialContext) locals left right available)
    (substitutions : Ctx.SubstEq env U target left right source)
    (entry : OriginalRichEntry frame index (Need.mk n demand) sourceType)
    (tailClosed : entry.tailAvailable.AtomClosed)
    (sourceF : OriginalCodeInductionAt env registry ordered entry.tailContext
      (Located.here (root := entry.originalDomain))
      ((Closure.close (entry.originalDomain.dependencyOrigin ordered)
          (entry.tailFrame.dependencyEnvironment ordered)).cost +
       (Closure.close (formation.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost))
    (observationR :
      richSchedule .expressionReindex
        ((Closure.close (entry.originalDomain.dependencyOrigin ordered)
          (entry.tailFrame.dependencyEnvironment ordered)).cost +
         (Closure.close (formation.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost →
      ∀ {rank} {profile : Profile rank} {footprint},
      RichObs sourceEnv env U registry target (.ref entry.originalDomain) entry.tailLocals entry.tailLeft profile footprint →
      footprint.Available entry.tailAvailable →
      Nonempty (CappedGeneratedQueryReply (frame.captureBase substitutions)
        (frame.captureBase substitutions).initialCaps
        (OriginalNestedDisplay.identity (frame.captureBase substitutions) formation
          ⟨_, _, _, root, initialContext, .assignedFormation location, rfl⟩)
        left right profile)) :
    Nonempty (RichCodeTransferResult env U registry target (.ref entry.originalDomain)
      formation locals entry.tailLeft left available true entry.support) := by
  have bound := richSchedule_strict (entry.comparison_bound ordered lookup levelWF formation) .expressionReindex .fundamental
  obtain ⟨reply⟩ := observationR bound (.code entry.certificate) entry.resources
  obtain ⟨fp, ⟨certificate⟩, resources⟩ := reply.freezeBase.code henv entry.certificate.formed
  have positive := (Closure.close (formation.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost_pos
  obtain ⟨semantics⟩ := sourceF target entry.tailLocals entry.tailLeft entry.tailRight entry.tailAvailable
    entry.tailFrame (Nat.lt_add_of_pos_right positive) tailClosed formed
    (entry.tailSubstitutions substitutions) entry.certificate entry.resources
  exact ⟨⟨fp, certificate, resources, by
    simpa only [entry.realizedType] using semantics.related.left_diagonal⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
