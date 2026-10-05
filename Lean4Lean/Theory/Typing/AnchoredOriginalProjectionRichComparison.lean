import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRecursiveSubstitution
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionCase
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeFormation
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQueryFrame

/-! The additional source-output contract required by rich projection
reindexing. Formation endpoints are computed from the actual original
endpoint tree. Natural projection fields and ambient assigned types are
kept distinct, including when an original conversion precedes the projection.
No coherence theorem or field-template producer is postulated here.
-/

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A rich code answer retains the exact destination formation occurrence.
Its source certificate may itself contain projected type observations. -/
structure RichCodeTransferResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression : VExpr} {leftLevel rightLevel : VLevel}
    (left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel))
    (right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel))
    (rightLocals : List Nat) (σ τ : Subst) (available : Valuation)
    (relevant : Bool) (profile : Profile n) where
  footprint : Footprint
  certificate : RichCert rightEnv env U registry target right rightLocals τ relevant profile footprint
  resources : footprint.Available available
  related : TypeRelated env U registry target (leftExpression.subst σ) (rightExpression.subst τ) profile

/-- A fixed original type equality needs this formation-query channel for
rich input as well as core input. This definition is an obligation, not an
upgrade of the existing hereditary fundamental theorem. -/
def RichCodeTransfer
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression : VExpr} {leftLevel rightLevel : VLevel}
    (left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel))
    (right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel))
    (leftLocals rightLocals : List Nat) (σ τ : Subst) (leftAvailable rightAvailable : Valuation) : Prop :=
  ∀ {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichCert leftEnv env U registry target left leftLocals σ relevant profile footprint →
    footprint.Available leftAvailable →
    Nonempty (RichCodeTransferResult env U registry target left right rightLocals σ τ rightAvailable
      relevant profile)

/-- Ordinary and captured source queries carry different finite resource
closures. A captured output chooses its own exact footprint and binder pack;
it is never required to fit a head valuation fixed before the query. -/
inductive RichAssignedQuery
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {displayed : List VExpr} {expression assigned : VExpr}
    (common : Subst) (available : Valuation) (locals : List Nat) (relevant : Bool) (profile : Profile n) :
    OriginalClosureDisplay sourceEnv U displayed expression assigned → Type where
  | ordinary {display : EndpointDisplay sourceEnv U displayed expression assigned}
      (certificate : RichCert sourceEnv env U registry target display.node.typeFormation.node locals
        (display.sourceSubst common) relevant profile footprint)
      (resources : footprint.Available (display.sourceValuation available)) :
      RichAssignedQuery env registry target common available locals relevant profile (.ordinary display)
  | captured {display : CapturedEndpointDisplay sourceEnv U displayed expression assigned}
      (certificate : RichCert sourceEnv env U registry target display.node.typeFormation.node (Locals.push locals)
        (display.sourceSubst common) relevant profile footprint)
      (frame : CapturedQueryFrame display env registry target common locals
        (fun index => available (display.map.liftVar index)) footprint outside) :
      RichAssignedQuery env registry target common available locals relevant profile (.captured display)

def RichAssignedQuery.footprint
    (query : RichAssignedQuery env registry target common available locals relevant profile display) : Footprint :=
  match query with
  | .ordinary (display := source) (footprint := required) _ _ => required.sourceLift source.map
  | .captured (display := source) _ frame => frame.footprint.sourceLift source.map

private theorem sourceLift_available {available : Valuation} {required : Footprint} {map : Lift}
    (resources : required.Available (fun index => available (map.liftVar index))) :
    (required.sourceLift map).Available available := by
  intro index need member
  obtain ⟨⟨oldIndex, oldNeed⟩, oldMember, same⟩ := List.mem_map.mp member
  cases same
  exact resources oldIndex need oldMember

theorem RichAssignedQuery.available {available : Valuation}
    (query : RichAssignedQuery env registry target common available locals relevant profile display) :
    query.footprint.Available available := by
  cases query with
  | ordinary certificate resources => exact sourceLift_available resources
  | captured certificate frame => exact sourceLift_available frame.available

/-- Comparison preserves both exact formation occurrences and emits a real
source query, including any finite newly required capture resources. -/
structure RichClosureCoherenceAnswer
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {U : Nat} {displayed : List VExpr}
    {expression leftType rightType : VExpr}
    (left : OriginalClosureDisplay leftEnv U displayed expression leftType)
    (right : OriginalClosureDisplay rightEnv U displayed expression rightType)
    (common : Subst) (available : Valuation) (leftLocals rightLocals : List Nat) where
  path : TypeConversion env U target (leftType.subst common) (rightType.subst common)
  queries : ∀ {relevant : Bool} {n : Nat} {profile : Profile n},
    RichAssignedQuery env registry target common available leftLocals relevant profile left →
    ∃ _output : RichAssignedQuery env registry target common available rightLocals relevant profile right,
      TypeRelated env U registry target (leftType.subst common) (rightType.subst common) profile

/-- Both formation closures use the actual captured environments. A capture
includes the original argument/domain bundle rather than just the source
formation spine. This bound contains no query-supplied numerical premise. -/
theorem richFormationPair_cost_le
    (left : OriginalClosureDisplay leftEnv U displayed expression leftType)
    (right : OriginalClosureDisplay rightEnv U displayed expression rightType) :
    (Closure.close left.node.typeFormation.node.origin left.environment).cost +
      (Closure.close right.node.typeFormation.node.origin right.environment).cost ≤
      left.cost + right.cost := by
  rw [left.cost_eq, right.cost_eq]
  exact Nat.add_le_add (left.node.typeFormation_cost_le left.environment)
    (right.node.typeFormation_cost_le right.environment)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
