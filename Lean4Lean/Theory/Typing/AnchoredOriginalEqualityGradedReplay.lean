import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Composition of original equality answers must interpret the actual raw
query returned by the preceding step. Its adapter recovers the requested
profile using that request's assigned-type support; raw and requested
profiles need not have the same rank. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades

/-- Interpret an equality at the concrete raw profile selected by a prior
query, then recover the requested relation and its actual right observer.
The final support comes from the original requested assigned formation. -/
noncomputable def OriginalEqualityQueryResult.adaptGraded
    {original : Derivation sourceEnv U source left right assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested support : Profile n}
    (typed : requested.HasType support)
    (code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support)
    (input : RichGradedResult sourceEnv env U registry target (.ref (.left original))
      locals σ available requested)
    (answer : OriginalEqualityQueryResult original env registry target locals σ τ available input.raw) :
    OriginalEqualityQueryResult original env registry target locals σ τ available requested where
  support := support
  related := by
    have adapted := input.adapter.termMap henv hscoped formed (Profile.HasType.raise input.bound typed)
      (code.raise henv input.bound) answer.related
    simpa only [lower_raised] using Related.lower henv input.bound formed adapted
  rightQuery := answer.rightQuery.adaptRequest henv hscoped formed input.bound input.adapter

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
