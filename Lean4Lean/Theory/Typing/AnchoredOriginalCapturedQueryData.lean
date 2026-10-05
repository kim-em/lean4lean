import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! Actual captured query operands and their finite ledger, shared by
world-aware application assembly and the older replay producers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure CapturedHeadQuery
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (common : List VExpr) (commonLeft commonRight : Subst) (expression : VExpr)
    (need : Need) (capacity : Nat) where
  depth : Nat
  scope : List VExpr
  insertion : Ctx.Lift' (.skipN .refl depth) common scope
  left : Subst
  right : Subst
  leftTail : Subst.lift_l (.skipN .refl depth) left = commonLeft
  rightTail : Subst.lift_l (.skipN .refl depth) right = commonRight
  caps : CaptureCaps
  capsTail : (fun i => caps ((Lift.skipN .refl depth).liftVar i)) = commonCaps
  assigned : VExpr
  display : OriginalNestedDisplay U scope (expression.lift' (.skipN .refl depth)) assigned
  ordered : display.sourceEnv.Ordered
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization display.graph env registry target locals left right available
  capped : CappedCaptureGenerated base caps left right display.graph realization.frame.raw
  rank : Nat
  bound : need.rank ≤ rank
  profile : Profile rank
  footprint : Footprint
  query : RichObs display.sourceEnv env U registry target display.node locals (display.raw.comp left) profile footprint
  resources : footprint.Available available
  adapter : GeneralNormalProfileAdapter env U registry target profile (raiseProfile rank bound need.profile)
  cost : (Closure.close (display.node.dependencyOrigin ordered)
    (realization.frame.dependencyEnvironment ordered)).cost ≤ capacity

def CapturedHeadQuery.enlarge
    (query : CapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity)
    (bound : capacity ≤ nextCapacity) :
    CapturedHeadQuery base commonCaps common commonLeft commonRight expression need nextCapacity :=
  { query with cost := Nat.le_trans query.cost bound }

inductive CapturedArgumentQueries
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (common : List VExpr) (commonLeft commonRight : Subst) (expression : VExpr)
    (capacity : Nat) : List Need → Type where
  | nil : CapturedArgumentQueries base commonCaps common commonLeft commonRight expression capacity []
  | cons (head : CapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity)
      (tail : CapturedArgumentQueries base commonCaps common commonLeft commonRight expression capacity needs) :
      CapturedArgumentQueries base commonCaps common commonLeft commonRight expression capacity (need :: needs)


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
