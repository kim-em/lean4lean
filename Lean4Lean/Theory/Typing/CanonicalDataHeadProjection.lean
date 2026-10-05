import Lean4Lean.Theory.Typing.CanonicalDataHeadApplication

/-! Projection context closure needs a constructor whose declaration cannot
also dispatch as a definition, native recursor, or primitive quotient head. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature
set_option backward.isDefEq.respectTransparency false

private theorem inert_step (definitions : registry.definitions name = none)
    (natives : registry.natives name = none)
    (quotient : registry.quotient = false ∨ name ≠ ``Quot.lift)
    (levels : List VLevel) (arguments : List VExpr) :
    step registry (mkApps (.const name levels) arguments) = none := by
  have legacy (args : List VExpr) :
      CanonicalHead.step registry (mkApps (.const name levels) args) = none := by
    simp only [CanonicalHead.step, spine_mkApps_exact (.const name levels) args rfl,
      CanonicalHead.spineStep, definitions, natives]
  have selection (args : List VExpr) :
      select registry (mkApps (.const name levels) args) = none := by
    simp only [select, spine_mkApps_exact (.const name levels) args rfl, natives]
    rcases quotient with absent | different
    · simp only [absent, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr different, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  suffices ∀ args : List VExpr, step registry (mkApps (.const name levels) args.reverse) = none by
    simpa only [List.reverse_reverse] using this arguments.reverse
  intro args
  induction args with
  | nil =>
    change step registry (.const name levels) = none
    simp only [step, show CanonicalHead.step registry (.const name levels) = none from legacy []]
  | cons argument args ih =>
    rw [List.reverse_cons]
    have last : mkApps (.const name levels) (args.reverse ++ [argument]) =
        .app (mkApps (.const name levels) args.reverse) argument := by
      simp only [mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have absent := legacy (args.reverse ++ [argument])
    rw [last] at absent ⊢
    simp only [step, absent, selection args.reverse, ih, Option.map_none]

theorem HeadInert.step (inert : HeadInert registry name)
    (levels : List VLevel) (arguments : List VExpr) :
    step registry (mkApps (.const name levels) arguments) = none :=
  inert_step inert.definition inert.native inert.quotient levels arguments

theorem project_none_of_step
    (lookup : registry.projections name = some info)
    (definitions : registry.definitions info.ctorName = none)
    (natives : registry.natives info.ctorName = none)
    (quotient : registry.quotient = false ∨ info.ctorName ≠ ``Quot.lift)
    (reduced : step registry expression = some out) :
    project registry name index expression = none := by
  simp only [project, lookup, bind, Option.bind_some]
  cases spine : expression.getAppFnArgs with
  | mk head args =>
    cases head <;> try rfl
    case const ctor levels =>
      simp only
      split
      · rename_i same
        subst ctor
        have reconstruct := mkApps_getAppFnArgs_eq expression
        change mkApps expression.getAppFnArgs.1 expression.getAppFnArgs.2 = expression at reconstruct
        rw [spine] at reconstruct
        have absent := inert_step definitions natives quotient levels args
        rw [reconstruct] at absent
        rw [absent] at reduced
        contradiction
      · rfl

theorem Trace.proj
    (lookup : registry.projections name = some info)
    (definitions : registry.definitions info.ctorName = none)
    (natives : registry.natives info.ctorName = none)
    (quotient : registry.quotient = false ∨ info.ctorName ≠ ``Quot.lift)
    (trace : Trace registry expression added result) :
    Trace registry (.proj name index expression) added (.proj name index result) := by
  induction trace with
  | refl => exact .refl
  | @next expression out added result reduced tail ih =>
    have noProject := project_none_of_step lookup definitions natives quotient reduced (index := index)
    have projected : step registry (.proj name index expression) = some (projMajor name index out) := by
      simp only [step, CanonicalHead.step, getAppFnArgs, getAppFnArgs.go,
        CanonicalHead.spineStep, noProject, reduced, Option.map_some]
    exact Trace.next (out := projMajor name index out) projected ih

end Lean4Lean.CanonicalDataHead
