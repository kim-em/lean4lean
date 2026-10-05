import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaElimination
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationCapture

/-! A finite application of a canonical Pi recipe at an actual original
argument. The replacement query is outside the canonical head's mask. This
is the single captured-head case, not a general substitution closure theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure CanonicalDeltaInstantiation
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env)
    (argument : EndpointState sourceEnv U source a A)
    (locals : List Nat) (σ : Subst) (B : VExpr)
    (relevant : Bool) (result : Profile n) where
  prototypeDomain : VExpr
  prototypeBody : VExpr
  ambient : Profile n
  rows : List (Key n × Profile n)
  key : Key n
  parentFootprint : Footprint
  parent : CanonicalDeltaElimination env U registry target strata source σ (.forallE A B)
    relevant (.pi prototypeDomain prototypeBody ambient rows) parentFootprint
  selected : (key, result) ∈ rows
  anchor : key.anchor = a.subst σ
  queryRank : Nat
  queryBound : n ≤ queryRank
  rawInput : Profile queryRank
  argumentFootprint : Footprint
  query : RichObs sourceEnv env U registry target argument locals σ rawInput argumentFootprint
  adapter : GeneralNormalProfileAdapter env U registry target rawInput
    (raiseProfile queryRank queryBound key.input)
  support : Profile n
  supportFootprint : Footprint
  certificate : RichCert sourceEnv env U registry target argument.typeFormation.node
    locals σ true support supportFootprint
  typed : key.input.HasType support

namespace CanonicalDeltaInstantiation
variable {argument : EndpointState sourceEnv U source a A}

noncomputable def depth
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result)
    (rank : Name → Nat) (control : Nat) : Nat :=
  max (recipe.parent.depth control)
    (max (recipe.query.stratifiedDepth rank control) (recipe.certificate.stratifiedDepth rank control))

def footprint
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result) : Footprint :=
  recipe.parentFootprint ++ recipe.argumentFootprint ++ recipe.supportFootprint

/-- The two actual original child answers suffice. No equality of assigned
original proof nodes, invented virtual source frame, or semantic recipe field
is used. A producer must obtain these answers at their original schedules. -/
theorem related
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target
      ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst τ)
      (.pi recipe.prototypeDomain recipe.prototypeBody recipe.ambient recipe.rows))
    (answer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available recipe.rawInput)
    (code : TypeRelated env U registry target (A.subst σ) (A.subst σ) recipe.support)
    (raw : env.IsDefEq U target (a.subst σ) (a.subst τ) (A.subst σ)) :
    TypeRelated env U registry target ((B.inst a).subst σ) ((B.inst a).subst τ) result := by
  have high := recipe.adapter.termMap henv hscoped formed
    (Profile.HasType.raise recipe.queryBound recipe.typed) (code.raise henv recipe.queryBound) answer.related
  have paired : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ)
      recipe.key.input recipe.support := by
    simpa only [lower_raised] using Related.lower henv recipe.queryBound formed high
  have output := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
    (by simpa only [subst] using whole) recipe.selected recipe.anchor raw paired
  simpa only [subst_inst, inst_lift_cons] using output

/-- The exact extra ledger which would fund future argument/support calls.
This is a raw-frame fact, NOT a positive generation constructor: an operative
R producer must also prove this selected frame fits its destination capacity.
In particular the unreserved result formation need not pay either child. -/
theorem reserved_children_lt
    (recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant result)
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (output : EndpointState sourceEnv U source (B.inst a) outputType) :
    let previous := frame.dependencyEnvironment ordered
    let ledger := [Closure.bundle (.close (argument.dependencyOrigin ordered) previous)
      (.close (argument.typeFormation.node.dependencyOrigin ordered) previous)]
    (Closure.close (argument.dependencyOrigin ordered) previous).cost +
      (Closure.close (argument.typeFormation.node.dependencyOrigin ordered) previous).cost <
      (Closure.close (output.dependencyOrigin ordered)
        ((frame.reserve ledger).dependencyEnvironment ordered)).cost := by
  dsimp only
  rw [OriginalRichFrame.reserve_environment]
  exact capturedVariable_bundle_lt (output.dependencyOrigin ordered)
    (argument.dependencyOrigin ordered) (argument.typeFormation.node.dependencyOrigin ordered)
    (frame.dependencyEnvironment ordered)

end CanonicalDeltaInstantiation
end Lean4Lean.AnchoredSource.Adapted
