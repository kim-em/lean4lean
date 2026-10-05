import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteSyntax

/-! Erase only the operational frames and reserves from the SAME finite
original type history. The reverse direction retains the actual route and
its well-formed reserve equality; no arbitrary skeleton is asserted to have
an operational realization. This is the boundary for a shared query recipe
whose positive syntax cannot import the high rich-frame grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

noncomputable def RawGeneratedTypeRoute.syntax
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) :
    OriginalTypeRouteSyntax env U common left right :=
  match route with
  | .identity display _ => .identity display
  | .same left right lf rf _ _ => .same left right lf rf
  | .equality graph original forward ordered below _ =>
      .equality graph original forward ordered below
  | .typedEquality graph original left agreement lf ordered below _ _ =>
      .typedEquality graph original left agreement lf ordered below
  | .trans first second => .trans first.syntax second.syntax
  | .assigned left right lf rf _ _ => .assigned left right lf rf
  | .piDomain left right below whole => .piDomain left right below whole.syntax
  | .applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph sourceOrdered headerOrdered
      sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound whole claimed =>
      .applyPi
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph)
        (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph)
        headerDomain rfl noBinders sourceOrdered headerOrdered sourceBelow headerBelow whole.syntax
termination_by structural route

/-- A recipe's history is realized by this exact operational route. In
particular all heterogeneous source/header frames, per-occurrence histories,
and computed reserves remain recoverable from `route`; equality of numeric
costs or a completed TypeRelated answer is not a substitute for this data. -/
structure OriginalTypeRouteRealization
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target common : List VExpr)
    (commonLeft commonRight : Subst)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (shape : OriginalTypeRouteSyntax env U common left right)
    (initial final : List Closure) where
  route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final
  exactSyntax : route.syntax = shape
  wellFormed : route.WellFormed

/-- The actual producer supplies the route, not a realization oracle for all
low syntax. Both original endpoints and both exact baseline ledgers are kept. -/
noncomputable def RawGeneratedTypeRoute.realizeSyntax
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (wellFormed : route.WellFormed) :
    OriginalTypeRouteRealization env U registry target common commonLeft commonRight route.syntax initial final :=
  ⟨route, rfl, wellFormed⟩

@[simp] theorem RawGeneratedTypeRoute.realizeSyntax_route
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (wellFormed : route.WellFormed) :
    (route.realizeSyntax wellFormed).route = route := rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
