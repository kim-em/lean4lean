import Lean4Lean.Theory.Typing.FormationCongruence

namespace Lean4Lean.VEnv
open VExpr

/-- Actual field substitutions contain equal parameters and prior projections
of equal majors. The latter are deliberately not required to be typed until
their occurrence is demanded by the selected field formation. -/
inductive FieldFormationCut (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop where
  | same (expression) : FieldFormationCut env U Γ expression expression
  | parameter : env.IsDefEqU U Γ left right → FieldFormationCut env U Γ left right
  | projection (name index) : env.IsDefEqU U Γ left right →
      FieldFormationCut env U Γ (.proj name index left) (.proj name index right)

theorem FieldFormationCut.realize
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (cut : FieldFormationCut env U Γ left right)
    (formed : OnCtx Γ (env.IsType U)) (typed : env.HasType U Γ left assigned) :
    env.IsDefEqU U Γ left right := by
  cases cut with
  | same => exact ⟨_, typed⟩
  | parameter equal => exact equal
  | projection name index equal => exact projectionCongruenceOfTyping ordered compatible formed typed equal

theorem FieldFormationCut.lift
    (ordered : env.Ordered) (cut : FieldFormationCut env U Γ left right) :
    FieldFormationCut env U (A :: Γ) left.lift right.lift := by
  cases cut with
  | same => exact .same _
  | parameter equal => exact .parameter (equal.weak ordered)
  | projection name index equal => exact .projection name index (equal.weak ordered)

theorem fieldFormationCuts
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (template : VExpr) (cuts : ∀ i, FieldFormationCut env U Γ (σ i) (τ i)) :
    FormationSubstitutionCuts env U Γ σ τ template := by
  induction template generalizing Γ σ τ with
  | bvar i => intro formed assigned typed; exact (cuts i).realize ordered compatible formed typed
  | sort | const | elim => trivial
  | app f a ihf iha => exact ⟨ihf cuts, iha cuts⟩
  | proj name index major ih => exact ih cuts
  | lam A body ihA ihB | forallE A body ihA ihB =>
    refine ⟨ihA cuts, ihB ?_⟩
    intro i
    cases i with
    | zero => exact .same _
    | succ i => exact (cuts i).lift ordered

theorem fieldArgumentCuts
    (parameters : List.Forall₂ (env.IsDefEqU U Γ) leftParams rightParams)
    (majors : env.IsDefEqU U Γ leftMajor rightMajor) (name : Name) (index : Nat) :
    List.Forall₂ (FieldFormationCut env U Γ)
      (leftParams ++ (List.range index).map (fun j => .proj name j leftMajor))
      (rightParams ++ (List.range index).map (fun j => .proj name j rightMajor)) := by
  induction parameters with
  | nil =>
    induction List.range index with
    | nil => exact .nil
    | cons j js ih => exact .cons (.projection name j majors) ih
  | cons equal rest ih => exact .cons (.parameter equal) ih

/-- Declaration-order substitution, including its genuine identity tail. -/
def fieldArgumentSubst (arguments : List VExpr) : Subst := fun i =>
  if h : i < arguments.length then arguments[arguments.length - 1 - i]
  else .bvar (i - arguments.length)

theorem fieldArgumentSubstCuts
    (arguments : List.Forall₂ (FieldFormationCut env U Γ) left right) :
    ∀ i, FieldFormationCut env U Γ (fieldArgumentSubst left i) (fieldArgumentSubst right i) := by
  intro i
  have length : left.length = right.length := by
    induction arguments with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  unfold fieldArgumentSubst
  by_cases bound : i < left.length
  · rw [dif_pos bound, dif_pos (by omega)]
    have atIndex : ∀ j (hl : j < left.length) (hr : j < right.length),
        FieldFormationCut env U Γ left[j] right[j] := by
      clear i bound length
      induction arguments with
      | nil => intro j h; simp at h
      | cons h hs ih =>
        intro j hl hr
        cases j with
        | zero => exact h
        | succ j => exact ih j (by simpa using hl) (by simpa using hr)
    have member := atIndex (left.length - 1 - i) (by omega) (by omega)
    simpa only [length] using member
  · rw [dif_neg bound, dif_neg (by omega), length]
    exact .same _

/-- Concrete sparse field demand production, including arbitrary nested
binders. Only parameter and MAJOR equalities are semantic inputs. -/
theorem fieldTemplateCongruence
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (parameters : List.Forall₂ (env.IsDefEqU U Γ) leftParams rightParams)
    (majors : env.IsDefEqU U Γ leftMajor rightMajor)
    (template : VExpr) (name : Name) (index : Nat)
    (formed : OnCtx Γ (env.IsType U))
    (typed : env.HasType U Γ
      (template.subst (fieldArgumentSubst
        (leftParams ++ (List.range index).map (fun j => .proj name j leftMajor)))) assigned) :
    env.IsDefEqU U Γ
      (template.subst (fieldArgumentSubst
        (leftParams ++ (List.range index).map (fun j => .proj name j leftMajor))))
      (template.subst (fieldArgumentSubst
        (rightParams ++ (List.range index).map (fun j => .proj name j rightMajor)))) := by
  exact FormationSubstitutionCuts.defeq ordered compatible template
    (fieldFormationCuts ordered compatible template
      (fieldArgumentSubstCuts (fieldArgumentCuts parameters majors name index))) formed typed

end Lean4Lean.VEnv
