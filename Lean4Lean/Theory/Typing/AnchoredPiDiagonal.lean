import Lean4Lean.Theory.Typing.AnchoredMinimalSupport

/-! Concrete diagonal Pi witnesses. Both constructors retain the chosen
context and renaming literally. The right constructor discharges the smaller
rank operations of Pi symmetry using the closed hereditary support laws.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
  {Γ : List VExpr} {left right A B : VExpr} {domain : Profile n}
  {rows : List (Key n × Profile n)}

/-- Keep the actual left display and the original raw-key domain bridges. -/
def PiWitness.left_diagonal
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left left A B domain rows where
  context := display.context
  map := display.map
  leftDomain := display.leftDomain
  leftBody := display.leftBody
  rightDomain := display.leftDomain
  rightBody := display.leftBody
  leftExposure := display.leftExposure
  rightExposure := display.leftExposure
  leftDomainType := display.leftDomainType
  rightDomainType := display.leftDomainType
  leftBodyType := display.leftBodyType
  rightBodyType := display.leftBodyType
  domains := .refl
  bodies := .refl
  prototypeDomainPath := display.prototypeDomainPath
  prototypeBodyPath := display.prototypeBodyPath
  domainRelated := TypeRelated.left_diagonal display.domainRelated
  rowDomains := display.rowDomains
  rowBodies := by
    intro key output hrow Δ ρ future x y admitted
    have h := (display.rowBodies key output hrow Δ ρ future x y admitted).1
    exact ⟨h, h, TypeRelated.left_diagonal h⟩

/-- Select the actual right display. Context, map, domains and bodies are
definitionally those of the old right endpoint. Domain-bridge reconstruction
uses only the proved closed semantic laws, with no caller-supplied operation. -/
def PiWitness.right_diagonal (henv : env.Ordered)
    (domainWF : domain.WF)
    (rowsWF : ∀ key output, (key, output) ∈ rows → output.WF)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ right right A B domain rows :=
  (PiWitness.symm henv
    (fun _ _ _ _ _ _ minimal _ hle H => H.focusMinimal henv minimal hle)
    (fun _ _ _ _ _ _ _ minimal typed first second =>
      first.composeMinimal henv minimal typed second)
    (fun _ _ _ _ hw H => H.symm henv hw)
    domainWF rowsWF display).left_diagonal

end Lean4Lean.AnchoredSemantics
