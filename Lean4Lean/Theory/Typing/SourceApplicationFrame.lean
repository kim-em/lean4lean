import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.Formation

/-! Select an application frame from the ORIGINAL typing derivation. Outer
conversion nodes and conversions on earlier function prefixes are traversed;
the selected children retain their actual natural domain and codomain. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency true

structure OriginalApplicationFrame (env : VEnv) (U : Nat) (Γ : List VExpr)
    (expression : VExpr) (position : Nat) where
  fn : VExpr
  argument : VExpr
  domain : VExpr
  body : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainLevelWF : domainLevel.WF U
  bodyLevelWF : bodyLevel.WF U
  domainTyped : env.HasTypeStrong U Γ domain (.sort domainLevel) true
  bodyTyped : env.HasTypeStrong U (domain :: Γ) body (.sort bodyLevel) true
  functionTypeTyped : env.HasTypeStrong U Γ (.forallE domain body)
    (.sort (.imax domainLevel bodyLevel)) true
  functionTyped : env.HasTypeStrong U Γ fn (.forallE domain body) true
  argumentTyped : env.HasTypeStrong U Γ argument domain true
  resultTyped : env.HasTypeStrong U Γ (body.inst argument) (.sort bodyLevel) true
  head : fn.getAppFnArgs.1 = expression.getAppFnArgs.1
  arguments_eq : fn.getAppFnArgs.2 = expression.getAppFnArgs.2.take position
  selected : expression.getAppFnArgs.2[position]? = some argument

/-- Every position of the actual application spine names actual original
function and argument children. No registered-domain type is imposed. -/
theorem HasTypeStrong.applicationFrame
    {env : VEnv} {U : Nat} {Γ : List VExpr} {expression assigned : VExpr} {structural : Bool}
    (original : env.HasTypeStrong U Γ expression assigned structural)
    (position : Nat) (bound : position < expression.getAppFnArgs.2.length) :
    Nonempty (OriginalApplicationFrame env U Γ expression position) := by
  induction original generalizing position with
  | app hu hv domain codomain whole function argument result
      ihD ihB ihWhole ihF ihA ihR =>
    rename_i Γ A u B v f a
    simp only [getAppFnArgs_app, List.length_append, List.length_singleton] at bound
    by_cases last : position = f.getAppFnArgs.2.length
    · subst position
      exact ⟨{
        fn := f, argument := a, domain := _, body := _, domainLevel := _, bodyLevel := _
        domainLevelWF := hu, bodyLevelWF := hv
        domainTyped := domain, bodyTyped := codomain, functionTypeTyped := whole
        functionTyped := function, argumentTyped := argument, resultTyped := result
        head := by simp only [getAppFnArgs_app]
        arguments_eq := by simp only [getAppFnArgs_app, List.take_left]
        selected := by simp only [getAppFnArgs_app, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero] }⟩
    · have before : position < f.getAppFnArgs.2.length := by omega
      obtain ⟨frame⟩ := ihF position before
      exact ⟨{ frame with
        head := by simpa only [getAppFnArgs_app] using frame.head
        arguments_eq := by simpa only [getAppFnArgs_app, List.take_append_of_le_length (Nat.le_of_lt before)]
          using frame.arguments_eq
        selected := by simpa only [getAppFnArgs_app, List.getElem?_append_left before]
          using frame.selected }⟩
  | base _ ih => exact ih position bound
  | defeq _ _ _ _ _ _ _ ih => exact ih position bound
  | bvar | sort' | const | elim | proj | lam | forallE =>
    simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.length_nil] at bound
    omega

/-- The chosen expression is literally the selected original argument. -/
theorem OriginalApplicationFrame.argument_eq
    (frame : OriginalApplicationFrame env U Γ expression position)
    (bound : position < expression.getAppFnArgs.2.length) :
    frame.argument = expression.getAppFnArgs.2[position] := by
  exact ((List.getElem?_eq_some_iff.mp frame.selected).2).symm

end Lean4Lean.VEnv
