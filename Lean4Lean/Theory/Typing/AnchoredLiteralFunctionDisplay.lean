import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredPiDiagonal

/-! A self display can be queried before its terminal context conversion.
The resulting world is a genuine inhabited proof insertion.  All private
domain/body syntax is retained; only the context declarations are converted.
This is the world needed to extend a source valuation along a function row. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}

def Exposure.beforeTerminal (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head) :
    Exposure env U registry Γ expression E.postContext ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := E.trace
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := .refl
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := (E.terminal.symm henv).path henv E.sound
  headType := (E.terminal.symm henv).isType henv E.headType

/-- Select the left self display before its final context conversion. -/
noncomputable def PiWitness.beforeTerminal (henv : env.Ordered)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left left A B domain rows where
  context := display.leftExposure.postContext
  map := display.map
  leftDomain := display.leftDomain
  leftBody := display.leftBody
  rightDomain := display.leftDomain
  rightBody := display.leftBody
  leftExposure := display.leftExposure.beforeTerminal henv
  rightExposure := display.leftExposure.beforeTerminal henv
  leftDomainType := (display.leftExposure.terminal.symm henv).isType henv display.leftDomainType
  rightDomainType := (display.leftExposure.terminal.symm henv).isType henv display.leftDomainType
  leftBodyType := ((display.leftExposure.terminal.symm henv).underBinder henv
    display.leftDomainType).isType henv display.leftBodyType
  rightBodyType := ((display.leftExposure.terminal.symm henv).underBinder henv
    display.leftDomainType).isType henv display.leftBodyType
  domains := .refl
  bodies := .refl
  prototypeDomainPath := (display.leftExposure.terminal.symm henv).path henv
    display.prototypeDomainPath
  prototypeBodyPath := ((display.leftExposure.terminal.symm henv).underBinder henv
    display.leftDomainType).path henv display.prototypeBodyPath
  domainRelated := (display.leftExposure.terminal.symm henv).code henv
    (TypeRelated.left_diagonal display.domainRelated)
  rowDomains := by
    intro key output member
    obtain ⟨support, typed, formed, bounded, path, bridge⟩ :=
      display.rowDomains key output member
    exact ⟨support, typed, formed, bounded,
      (display.leftExposure.terminal.symm henv).path henv path,
      (display.leftExposure.terminal.symm henv).code henv bridge⟩
  rowBodies := by
    intro key output member Δ ρ future x y admitted
    obtain ⟨oldΔ, oldFuture, changed⟩ := display.leftExposure.terminal.pushFuture henv future
    have old := (display.rowBodies key output member oldΔ ρ oldFuture x y
      (changed.admitted henv admitted)).1
    have current := (changed.symm henv).code henv old
    exact ⟨current, current, current.left_diagonal⟩

/-- Apply one fixed actual display, independently of how the function's
semantic proof originally selected its covering row. -/
def FunctionRowBehavior
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right type : VExpr)
    (key : Key n) (output : Atom n) (resultType : Profile n)
    (display : PiWitness env U registry (relations env U registry n)
      Γ type type A B domain rows) : Prop :=
  ∀ Δ ρ, FutureInsertion env U display.context Δ ρ → ∀ x y,
    Admitted env U registry Δ (key.rename (display.map.comp ρ)) x y →
    Related env U registry Δ
      (.app (left.lift' (display.map.comp ρ)) x)
      (.app (left.lift' (display.map.comp ρ)) y)
      ((display.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (display.map.comp ρ)))
      (resultType.rename (display.map.comp ρ)) ∧
    Related env U registry Δ
      (.app (right.lift' (display.map.comp ρ)) x)
      (.app (right.lift' (display.map.comp ρ)) y)
      ((display.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (display.map.comp ρ)))
      (resultType.rename (display.map.comp ρ)) ∧
    Related env U registry Δ
      (.app (left.lift' (display.map.comp ρ)) x)
      (.app (right.lift' (display.map.comp ρ)) x)
      ((display.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (display.map.comp ρ)))
      (resultType.rename (display.map.comp ρ))

/-- The finite chosen row, with its literal proof-insertion world exposed. -/
structure LiteralFunctionDisplay
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right type : VExpr)
    (key : Key n) (output : Atom n) (typeProfile : Profile (n + 1)) where
  A : VExpr
  B : VExpr
  domain : Profile n
  rows : List (Key n × Profile n)
  resultType : Profile n
  typeMember : (AtomData.pi A B domain rows : Atom (n + 1)) ∈ typeProfile.atoms
  rowMember : (key, resultType) ∈ rows
  typed : (Profile.singleton output).HasType resultType
  display : PiWitness env U registry (relations env U registry n)
    Γ type type A B domain rows
  insertion : ProofInsertion env U Γ display.context display.map
  behavior : FunctionRowBehavior env U registry Γ left right type key output resultType display

theorem FunctionBehavior.literalDisplay (henv : env.Ordered)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output typeProfile) :
    Nonempty (LiteralFunctionDisplay env U registry Γ left right type key output typeProfile) := by
  obtain ⟨_, A, B, domain, rows, result, member, row, typed, display, behavior⟩ := H
  refine ⟨{
    A := A
    B := B
    domain := domain
    rows := rows
    resultType := result
    typeMember := member
    rowMember := row
    typed := typed
    display := display.beforeTerminal henv
    insertion := ?_
    behavior := ?_ }⟩
  · have insertion := display.leftExposure.generated.comp display.leftExposure.post henv
    rw [display.leftExposure.map_eq] at insertion
    exact insertion
  · intro Δ ρ future x y admitted
    obtain ⟨oldΔ, oldFuture, changed⟩ := display.leftExposure.terminal.pushFuture henv future
    obtain ⟨first, second, cross⟩ := behavior oldΔ ρ oldFuture x y
      (changed.admitted henv admitted)
    exact ⟨(changed.symm henv).term henv first, (changed.symm henv).term henv second,
      (changed.symm henv).term henv cross⟩

end Lean4Lean.AnchoredSemantics
