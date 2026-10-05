import Lean4Lean.Theory.Typing.DefinitionOuterStage

/-! Actual transparent-definition histories need not share an equation order.
Two independent definitions admit opposite declaration orders, and the retained
pre-equation headers inherit these opposite dependencies. This refutes a rank
on equations that treats every stored header equation as an earlier dependency;
it does not refute semantic interpretation of these sort-shaped bodies. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

namespace CrossedDefinitionHeaders

def value (name : Name) : VDefVal where
  name := name
  uvars := 0
  type := .sort (.succ .zero)
  value := .sort .zero

def bare (name : Name) : VEnv where
  constants selected := if name = selected then some (value name).toVConstant else none
  defeqs _ := False

def one (name : Name) : VEnv := (bare name).addDefEq (value name).toDefEq

def header (first second : Name) : VEnv where
  constants selected := if first = selected ∨ second = selected then
    some (value first).toVConstant else none
  defeqs rule := rule = (value second).toDefEq

def both (first second : Name) : VEnv where
  constants selected := if first = selected ∨ second = selected then
    some (value first).toVConstant else none
  defeqs rule := rule = (value first).toDefEq ∨ rule = (value second).toDefEq

theorem value_wf (env : VEnv) (name : Name) : (value name).WF env :=
  .sortDF trivial trivial rfl

theorem bare_install (name : Name) :
    (∅ : VEnv).addConst name (value name).toVConstant = some (bare name) := rfl

theorem one_history (name : Name) : (one name).WF' [.def (value name)] :=
  .decl (.def (value_wf _ _) (bare_install _)) .empty

theorem header_install (first second : Name) (distinct : first ≠ second) :
    (one second).addConst first (value first).toVConstant = some (header first second) := by
  simp only [VEnv.addConst, one, bare, VEnv.addDefEq, if_neg (Ne.symm distinct)]
  apply congrArg some
  apply VEnv.ext
  · funext selected
    by_cases left : first = selected <;> by_cases right : second = selected <;>
      simp [header, value, left, right]
  · funext rule
    apply propext
    simp [header]
  · rfl
  · rfl

theorem complete (first second : Name) :
    (header first second).addDefEq (value first).toDefEq = both first second := rfl

theorem both_history (first second : Name) (distinct : first ≠ second) :
    (both first second).WF' [.def (value first), .def (value second)] :=
  .decl (.def (value_wf _ _) (header_install first second distinct)) (one_history _)

theorem commute (first second : Name) : both first second = both second first := by
  apply VEnv.ext
  · funext selected
    simp [both, value, or_comm]
  · funext rule
    exact propext (Or.comm)
  · rfl
  · rfl

def origin (first second : Name) (distinct : first ≠ second) :
    DefinitionDeclarationOrigin (both first second)
      [.def (value first), .def (value second)] (value first) where
  base := one second
  installed := both first second
  earlierDeclarations := [.def (value second)]
  history := one_history second
  declaration := .def (value first)
  stage := .single (value_wf _ _) (header_install first second distinct)
  laterDeclarations := []
  declarations_eq := rfl
  installedBelow := .rfl

/-- This retained pre-equation header contains the other definition's exact
installed equation, although the two final environments are identical. -/
theorem other_installed (first second : Name) (distinct : first ≠ second) :
    (origin first second distinct).stage.header.defeqs (value second).toDefEq := rfl

/-- Even a rank selected after seeing the final well-formed environment
cannot orient all actual stored definition origins by their header equations. -/
theorem no_stored_header_equation_rank (first second : Name) (distinct : first ≠ second) :
    ¬ ∃ rank : VDefEq → Nat,
      ∀ {declarations definition}
        (stored : DefinitionDeclarationOrigin (both first second) declarations definition)
        {rule : VDefEq}, stored.stage.header.defeqs rule →
          rank rule < rank definition.toDefEq := by
  rintro ⟨rank, decrease⟩
  have oneStep := decrease (origin first second distinct) (other_installed first second distinct)
  let reversed : DefinitionDeclarationOrigin (both first second)
      [.def (value second), .def (value first)] (value second) :=
    (origin second first (Ne.symm distinct)).metadata (by
      rw [commute second first]
      exact .rfl)
  have reversedMember : reversed.stage.header.defeqs (value first).toDefEq := by
    exact other_installed second first (Ne.symm distinct)
  have otherStep := decrease reversed reversedMember
  exact Nat.lt_irrefl _ (Nat.lt_trans oneStep otherStep)

end CrossedDefinitionHeaders
end Lean4Lean.VEnv
