import Lean4Lean.Theory.Typing.AnchoredDataExposure

/-! A declared family head is inert when its tag is absent from computation
registries. The arguments are arbitrary: substitution may change their heads
without introducing reduction at the family application itself. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr

theorem step_family
    (definitions : registry.definitions name = none)
    (natives : registry.natives name = none)
    (quotient : name ≠ ``Quot.lift)
    (head : expression.getAppFnArgs.1 = .const name levels) :
    step registry expression = none := by
  induction expression with
  | app function argument ih _ =>
    have functionHead : function.getAppFnArgs.1 = .const name levels := by
      simpa only [getAppFnArgs_app] using head
    have legacy : CanonicalHead.step registry.toRegistry (.app function argument) = none := by
      simp only [CanonicalHead.step, head, CanonicalHead.spineStep, definitions, natives]
    have selected : select registry function = none := by
      unfold select
      cases found : function.getAppFnArgs with
      | mk fn args =>
        have equal : fn = .const name levels := by simpa only [found] using functionHead
        subst fn
        simp [natives, quotient]
    simp only [step, legacy, selected, ih functionHead, Option.map_none]
  | const actual actualLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    simp only [step, CanonicalHead.step, getAppFnArgs_const,
      CanonicalHead.spineStep, definitions, natives]
  | bvar | sort | forallE | lam | elim | proj =>
    simp only [getAppFnArgs] at head
    contradiction

end Lean4Lean.CanonicalDataHead
