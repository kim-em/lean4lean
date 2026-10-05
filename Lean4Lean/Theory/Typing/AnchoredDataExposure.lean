import Lean4Lean.Theory.Typing.CanonicalDataHeadTrace
import Lean4Lean.Theory.Typing.TypedWorldMixed
import Lean4Lean.Theory.Typing.NativeCaptureTransport

/-! Raw typed data displays and declaration-derived constructor results.
These types are independent of all anchored semantic relations. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature

/-- The term counterpart of `Exposure`: the trace displays a value at its
actual assigned type, rather than a type code at a universe. -/
structure ConstructorExposure (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (expression type : VExpr) (Δ : List VExpr) (ρ : Lift)
    (head : VExpr) where
  added : List VExpr
  result : VExpr
  postMap : Lift
  trace : CanonicalDataHead.Trace registry expression added result
  generated : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length)
  postContext : List VExpr
  post : ProofInsertion env U (added ++ Γ) postContext postMap
  terminal : ContextChain env U postContext Δ
  map_eq : (Lift.skipN .refl added.length).comp postMap = ρ
  result_eq : result.lift' postMap = head
  sound : env.IsDefEq U Δ (expression.lift' ρ) head (type.lift' ρ)

/-- The result template comes from the actual constant lookup and its full
literal declaration telescope. Neither endpoint may propose an arbitrary
family result. Parameters and fields are supplied in declaration order. -/
structure ConstructorResultHeader (env : VEnv) (constructor family : Name)
    (levels : List VLevel) (arguments : List VExpr) where
  info : VConstant
  lookup : env.constants constructor = some info
  domains : List VExpr
  familyLevels : List VLevel
  familyArguments : List VExpr
  telescope : info.type.instL levels =
    wrapForalls domains (mkApps (.const family familyLevels) familyArguments)
  saturated : domains.length = arguments.length

namespace ConstructorResultHeader
variable (header : ConstructorResultHeader env constructor family levels arguments)

def result : VExpr := instantiateParams (mkApps (.const family header.familyLevels)
  header.familyArguments) arguments

private theorem closedBody {domains : List VExpr} {body : VExpr}
    (closed : (wrapForalls domains body).ClosedN count) :
    body.ClosedN (count + domains.length) := by
  induction domains generalizing count with
  | nil => exact closed
  | cons domain domains ih =>
    have body := ih (show (wrapForalls domains body).ClosedN (count + 1) from closed.2)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using body

theorem resultScoped (henv : env.Ordered) :
    (mkApps (.const family header.familyLevels) header.familyArguments).ClosedN arguments.length := by
  obtain ⟨u, type⟩ := henv.constWF header.lookup
  have closed := (VExpr.WF.closedN henv ⟨_, type⟩ trivial).instL (ls := levels)
  rw [header.telescope] at closed
  simpa only [List.length_nil, Nat.zero_add, header.saturated] using closedBody closed

def rename (ρ : Lift) : ConstructorResultHeader env constructor family levels
    (arguments.map (·.lift' ρ)) :=
  { header with saturated := by simpa only [List.length_map] using header.saturated }

theorem result_rename (henv : env.Ordered) (ρ : Lift) :
    (header.rename ρ).result = header.result.lift' ρ := by
  exact (VEnv.instantiateParams_lift' (header.resultScoped henv) ρ).symm

end ConstructorResultHeader

end Lean4Lean.AnchoredSemantics
