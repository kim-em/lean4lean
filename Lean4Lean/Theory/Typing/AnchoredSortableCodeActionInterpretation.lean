import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionTyping
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction
import Lean4Lean.Theory.Typing.AnchoredSortableCodeIntroduction

/-! Code actions have a computed assigned-type support at their result rank.
All its universe covers come from the actual input support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCodeAction.termMap
    {profile support : Profile n} {nextProfile : Profile m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (formed : profile.HasType (.sort relevant))
    (typed : profile.HasType support)
    (typeCode : TypeRelated env U registry target assigned assigned support)
    (related : Related env U registry target left right assigned profile support) :
    Related env U registry target left right assigned nextProfile (support.flatSortsAt m) := by
  have flattened : profile.HasType (Profile.sortsAt n support.sortFlags) :=
    formed.flatSorts typed
  exact Related.of_sortable_code henv (action.preservesSort formed)
    (action.typedAtSorts flattened)
    (action.codeMap henv hscoped (related.code_of_sortable henv hscoped hTarget formed))
    (typeCode.flatSortsAt henv)

/-- A directional code transformation can use the actual final type
capability. In particular a contravariant argument transformation needs no
inverse operation on the old function's domain certificate. -/
theorem SortableCodeAction.termMapAt
    {profile support : Profile n} {nextProfile finalSupport : Profile m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (formed : profile.HasType (.sort relevant))
    (typed : nextProfile.HasType finalSupport)
    (typeCode : TypeRelated env U registry target assigned assigned finalSupport)
    (related : Related env U registry target left right assigned profile support) :
    Related env U registry target left right assigned nextProfile finalSupport :=
  Related.of_sortable_code henv (action.preservesSort formed) typed
    (action.codeMap henv hscoped (related.code_of_sortable henv hscoped hTarget formed))
    typeCode

end Lean4Lean.AnchoredSource.Adapted
