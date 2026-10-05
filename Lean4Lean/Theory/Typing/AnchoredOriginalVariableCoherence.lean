import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplayTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn

/-! The variable case of original endpoint comparison uses context lookup,
not a type-uniqueness theorem. After original conversions are exposed, two
displays of the same variable have literally equal displayed lookup types,
even when their original source contexts and weakening maps differ. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

structure BVarView
    {node : EndpointState env U context (.bvar index) assigned}
    (start : Located root node) where
  sourceType : VExpr
  level : VLevel
  lookup : Lookup context index sourceType
  levelWF : level.WF U
  formation : EndpointState env U context sourceType (.sort level)
  location : Located root (.bvar lookup levelWF formation)
  prefix_eq : location.binderPrefix = start.binderPrefix
  cost_le : ∀ initial,
    (Closure.close (EndpointState.bvar lookup levelWF formation).origin
      (location.environment initial)).cost ≤
      (Closure.close node.origin (start.environment initial)).cost

noncomputable def bvarView
    {node : EndpointState env U context (.bvar index) assigned}
    (start : Located root node) : BVarView start := by
  obtain ⟨type, head, path, normal, prefixEq, cost⟩ := headView start
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | bvar lookup levelWF formation =>
    exact ⟨_, _, lookup, levelWF, formation, path, prefixEq, cost⟩

/-- A code query at the natural variable type is charged to the actual
formation child, including its source context, before conversion replay. -/
theorem BVarView.formation_cost_lt
    {node : EndpointState env U context (.bvar index) assigned}
    {start : Located root node} (view : BVarView start) (initial : List Closure) :
    (Closure.close view.formation.origin (view.location.environment initial)).cost <
      (Closure.close node.origin (start.environment initial)).cost :=
  Nat.lt_of_lt_of_le (original_child_same_environment
    (Origin.rule_child (by simp)) (view.location.environment initial)) (view.cost_le initial)

/-- Equality of displayed variables determines equality of their natural
lookup types. The two source contexts need not be equal. -/
theorem displayedLookupTypes_eq
    (left : Lookup leftSource leftIndex leftType)
    (right : Lookup rightSource rightIndex rightType)
    (leftInsertion : Ctx.Lift' leftMap leftSource common)
    (rightInsertion : Ctx.Lift' rightMap rightSource common)
    (same : (VExpr.bvar leftIndex).lift' leftMap = (VExpr.bvar rightIndex).lift' rightMap) :
    leftType.lift' leftMap = rightType.lift' rightMap := by
  have indexEq : leftMap.liftVar leftIndex = rightMap.liftVar rightIndex := VExpr.bvar.inj same
  have leftLookup := left.weak' leftInsertion
  rw [indexEq] at leftLookup
  exact leftLookup.uniq (right.weak' rightInsertion)

/-- The variable's natural raw type comparison is independent of all
observation support, including an empty query. -/
theorem displayedLookupTypes_path
    (left : Lookup leftSource leftIndex leftType)
    (right : Lookup rightSource rightIndex rightType)
    (leftInsertion : Ctx.Lift' leftMap leftSource commonSource)
    (rightInsertion : Ctx.Lift' rightMap rightSource commonSource)
    (same : (VExpr.bvar leftIndex).lift' leftMap = (VExpr.bvar rightIndex).lift' rightMap)
    {common σ τ : Subst}
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ) :
    TypeConversion env U target (leftType.subst σ) (rightType.subst τ) := by
  have equal := realized_between_displays
    (displayedLookupTypes_eq left right leftInsertion rightInsertion same)
    leftRealization rightRealization
  rw [equal]
  exact .refl

/-- The natural variable comparison needs one actual formation answer on
the left. Lookup equality transports its returned source certificate into
the right source context without invoking type uniqueness or interpreting a
newly weakened derivation. Conversion routes are handled by `compareHeads`.
-/
theorem BVarView.compareNatural
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.bvar leftIndex) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.bvar rightIndex) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : BVarView leftStart) (rightView : BVarView rightStart)
    (leftInsertion : Ctx.Lift' leftMap leftSource commonSource)
    (rightInsertion : Ctx.Lift' rightMap rightSource commonSource)
    (same : (VExpr.bvar leftIndex).lift' leftMap = (VExpr.bvar rightIndex).lift' rightMap)
    {target : List VExpr} {leftLocals : List Nat} {σ τ common : Subst}
    {leftAvailable rightAvailable commonAvailable : Valuation}
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index))
    (commonLocals rightLocals : List Nat)
    {profile : Profile n}
    (answer : CodeTransferResult env U registry target leftLocals σ σ leftAvailable
      leftView.sourceType leftView.sourceType profile) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      leftView.sourceType rightView.sourceType profile) := by
  have typeEq := displayedLookupTypes_eq leftView.lookup rightView.lookup
    leftInsertion rightInsertion same
  obtain ⟨required, ⟨certificate⟩, resources⟩ := OriginalFactorCut.CodeCert.betweenDisplays answer.certificate
    leftMap rightMap common leftRealization rightRealization typeEq commonLocals rightLocals
    answer.available leftAvailableEq rightAvailableEq
  have targetTypeEq := realized_between_displays typeEq leftRealization rightRealization
  exact ⟨⟨required, certificate, resources, by
    simpa only [targetTypeEq] using answer.related⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
