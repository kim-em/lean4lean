import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteBoundary
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations

/-! Exact primitive call lists of an executable route boundary. Restriction
uses sublists, so neither multiplicity nor order of a retained budget is
silently changed when interpreting a child route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private environment_worlds_mpr from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem callBelow_of_sublist {count : Nat} {calls reserve parent : List (World count)}
    (selected : calls.Sublist reserve) (smaller : CallBelow count reserve parent) :
    CallBelow count calls parent := by
  suffices sameOrSmaller : calls = reserve ∨ CallBelow count calls reserve by
    rcases sameOrSmaller with rfl | lower
    · exact smaller
    · exact lower.trans smaller
  clear smaller
  induction selected with
  | slnil => exact .inl rfl
  | @cons xs ys a selected ih =>
    have remove : CallBelow count ys (a :: ys) :=
      .single (.head (replacement := []) (by intro _ member; cases member))
    rcases ih with rfl | lower
    · exact .inr remove
    · exact .inr (lower.trans remove)
  | cons_cons a selected ih =>
    rcases ih with rfl | lower
    · exact .inl rfl
    · exact .inr (lower.cons a)

namespace RawGeneratedTypeRoute.WorldBoundary

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
  {commonLeft commonRight : Subst} {strata : EquationStratification env}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
  {inputs : route.WorldInputs strata}
  {leftControls : OriginalWorldControls strata left.sourceEnv}
  {rightControls : OriginalWorldControls strata right.sourceEnv}
  {leftWorld : WorldEnvironmentProvenance strata U initial}
  {rightWorld : WorldEnvironmentProvenance strata U final}

/-- Primitive calls read their controls and baselines from the SAME boundary
used by execution; these are not arbitrary externally supplied bounds. -/
noncomputable def calls
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    List (World strata.rules.length) := by
  induction boundary with
  | identity => exact []
  | same left right _ _ _ lc rc lw rw _ => exact
      [originalCallWorld lc .expressionReindex left.node lw,
       originalCallWorld rc .expressionReindex right.node rw]
  | assigned left right _ _ _ lc rc lw rw _ => exact
      [originalCallWorld lc .assignedComparison left.node lw,
       originalCallWorld rc .assignedComparison right.node rw]
  | equality _ original _ _ _ controls world => exact
      [originalCallWorld controls .fundamental (.ref (.left original)) world]
  | typedEquality _ original left _ _ _ _ _ lc rc lw rw _ => exact
      [originalCallWorld lc .expressionReindex left.node lw,
       originalCallWorld rc .expressionReindex (.ref (.left original)) rw,
       originalCallWorld rc .fundamental (.ref (.left original)) rw]
  | trans _ _ before after => exact before ++ after
  | piDomain _ _ _ _ child => exact child
  | applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceOrdered headerOrdered sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound
      whole claimedSeedReserve sourceControls headerControls sourceWorld priorWorld ownerWorld sourceAdmission wholeInputs
      boundary claim child =>
      let application := originalCallWorld sourceControls .fundamental
        (.app hu hv (.ref domain) body function argument result) sourceWorld
      let header := originalCallWorld headerControls .fundamental
        (.pi hcu hdv (.ref headerDomain) headerBody) priorWorld
      exact child ++ [application, application, header, header]

/-- Exact agreement with the positive history reserve, including repeated
application/header originals. -/
theorem calls_eq_reserve
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    boundary.calls = (route.worldReserve inputs).worlds := by
  induction boundary with
  | identity =>
    simp only [calls, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
    rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
    rfl
  | same | assigned | equality | typedEquality =>
    simp only [calls, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
    rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
    rfl
  | trans before after ihBefore ihAfter =>
    simp only [calls, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
    rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
    rw [WorldEnvironmentProvenance.worlds_append]
    exact congr (congrArg List.append ihBefore) ihAfter
  | piDomain left right below child ih =>
    simp only [calls, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
    rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
    exact ih
  | applyPi =>
    simp only [calls, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
    rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
    rw [WorldEnvironmentProvenance.worlds_append]
    first | exact congrArg (· ++ _) ‹_ = _› | congr 1

/-- Both admission and strict recursive funding are inherited by an exact
sublist of the retained reserve. The sponsor frontier is unchanged. -/
theorem selectFunding
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (frontier parent : List (World strata.rules.length))
    (sponsored : Sponsored frontier (route.worldReserve inputs).worlds)
    (smaller : CallBelow strata.rules.length (frontier ++ (route.worldReserve inputs).worlds) parent)
    {selected : List (World strata.rules.length)} (present : selected.Sublist boundary.calls) :
    Sponsored frontier selected ∧ CallBelow strata.rules.length (frontier ++ selected) parent := by
  rw [← boundary.calls_eq_reserve] at sponsored smaller
  exact ⟨fun world member => sponsored world (present.subset member),
    callBelow_of_sublist (present.append_left frontier) smaller⟩

end RawGeneratedTypeRoute.WorldBoundary
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
