import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionValue
import Lean4Lean.Theory.Typing.AnchoredOriginalCutFrames
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginIntroduction
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginReduction

/-! Raw field origins come from the original projection rule even when the
requested field input is empty. A fixed smaller comparison aligns its hidden
family with the common original major type; no semantic atom is selected.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def originalDisplay
    (initial : ContextDerivation sourceEnv U source)
    (reference : EndpointRef sourceEnv U source expression assigned) :
    EndpointDisplay sourceEnv U source expression assigned :=
  .identity initial (.ref reference) (.ofLocation .here initial)

/-- This comparison uses actual original references on both sides. In an
eta application, `common` is the retained major premise and the second
reference is the major child found inside the actual constructor argument. -/
theorem ProjectionHead.originAt
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major assigned commonType : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (common : EndpointRef sourceEnv U source major commonType)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (frame : OriginalQueryFrame env registry target initial locals σ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (comparison : DisplayCoherence env U registry
      (originalDisplay initial common) (originalDisplay initial (.right head.major))) :
    Nonempty (RankedData.ProjectionOrigin env U target head.info name index
      (major.subst σ) (commonType.subst σ) (assigned.subst σ)) := by
  let leftFrame : DisplayFits env registry target (originalDisplay initial common)
      σ available locals := frame.display (.ref common) (.ofLocation .here initial)
  let rightFrame : DisplayFits env registry target (originalDisplay initial (.right head.major))
      σ available locals := frame.display (.ref (.right head.major)) (.ofLocation .here initial)
  have answer := comparison target σ available locals locals closed formed leftFrame rightFrame
  let original := RankedData.ProjectionOrigin.ofRule (below.projections head.registered)
    head.levelsWF head.levelCount head.parameterCount head.indexCount head.selected
    (head.field.sound.defeq.mono below) (head.major.forget.defeq.mono below)
    head.closed head.relevance
  let natural := original.substitute henv formed frame.substitutions
  let aligned := natural.convertAssignedType answer.path.symm
  have fieldPath := head.route.targetPath henv below formed frame.substitutions
  exact ⟨{ aligned with fieldPath := aligned.fieldPath.trans fieldPath.symm }⟩

/-- The origin remains available at a new major through an actual original
equality. This supplies raw empty-field coverage without requiring a source
projection observer at the new major. -/
theorem ProjectionHead.originPairAt
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major next assigned commonType : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (equal : Derivation sourceEnv U source major next commonType)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (frame : OriginalQueryFrame env registry target initial locals σ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (comparison : DisplayCoherence env U registry
      (originalDisplay initial (.left equal)) (originalDisplay initial (.right head.major))) :
    Nonempty (RankedData.ProjectionOrigin env U target head.info name index
      (major.subst σ) (commonType.subst σ) (assigned.subst σ)) ∧
    Nonempty (RankedData.ProjectionOrigin env U target head.info name index
      (next.subst τ) (commonType.subst σ) (assigned.subst σ)) := by
  obtain ⟨origin⟩ := head.originAt (.left equal) henv below initial frame closed formed comparison
  have pair := (equal.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨⟨origin⟩, ⟨origin.replaceMajor pair⟩⟩

/-- A comparison against a projected constructor argument is strictly below
the actual structure-eta rule. The head's hidden major is already charged
to that constructor child's original closure. -/
theorem etaProjectionOrigin_schedule
    {env : VEnv} {U : Nat} {source : List VExpr} {name : Name} {info : VProjectionInfo}
    {parameters : List VExpr} {levels : List VLevel} {expression : VExpr}
    (registered : env.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation env U source expression expression (mkApps (.const name levels) parameters))
    (constructor : Derivation env U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields)
    (initial : ContextDerivation env U source) :
    let head := projectionHead (etaProjectionArgument constructor index bound).node
    schedule .coherence
      ((originalDisplay initial (.left major)).cost +
        (originalDisplay initial (.right head.major)).cost) <
      schedule .fundamental (Closure.close
        (Derivation.structEta registered parameterCount noIndices major constructor).origin
        initial.closures).cost := by
  dsimp only
  apply schedule_strict
  have headBound := (projectionHead (etaProjectionArgument constructor index bound).node).route.weight_le
  have majorBound := original_child_same_environment
    (Origin.rule_child (children := [
      (projectionHead (etaProjectionArgument constructor index bound).node).field.origin,
      (projectionHead (etaProjectionArgument constructor index bound).node).major.origin])
      (child := (projectionHead (etaProjectionArgument constructor index bound).node).major.origin)
      (by simp)) initial.closures
  have nodeBound := Nat.mul_le_mul_right (1 + environmentCost initial.closures) headBound
  have constructorBound := (etaProjectionArgument constructor index bound).cost_le initial.closures
  have smaller := Nat.lt_of_lt_of_le majorBound (Nat.le_trans nodeBound constructorBound)
  have parent := original_two_children major.origin constructor.origin [] initial.closures
  exact Nat.lt_trans (Nat.add_lt_add_left smaller _) parent

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
