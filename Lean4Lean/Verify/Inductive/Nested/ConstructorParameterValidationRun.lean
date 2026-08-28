import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterNativePrefix

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Every member of a successfully traversed list has itself completed
successfully.  This is the small executable inversion needed to select one
constructor from the retained whole-block validation run. -/
private theorem listForM_eq_ok_of_mem
    (step : α → Except ε Unit) :
    ∀ {items : List α}, items.forM step = .ok () →
      ∀ {item}, item ∈ items → step item = .ok () := by
  intro items hrun item hitem
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
    simp only [List.forM] at hrun
    cases hhead : step head with
    | error err =>
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    | ok value =>
      rcases value with ⟨⟩
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hhead
      · exact ih hrun htail

/-- Select the exact common-parameter-prefix run for one source constructor
from the successful native validation of the complete mutual block. -/
theorem validateRestoredConstructorParameters.loop_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
      fuel result.lctx {} ctor.name result.params ctor.type 0
        fuel.inductiveFuel = .ok () := by
  unfold Lean4Lean.validateRestoredConstructorParameters.run at hrun
  have hfamily := listForM_eq_ok_of_mem
    (fun type : InductiveType => type.ctors.forM fun ctor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel)
        (TypeChecker.checkType ctor.type)
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel)
    hrun htype
  have hconstructor := listForM_eq_ok_of_mem
    (fun ctor : Constructor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel)
        (TypeChecker.checkType ctor.type)
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel)
    hfamily hctor
  change (TypeChecker.M.run env (safety := safety) (lctx := {})
    (lparams := lparams) (fuel := fuel)
    (TypeChecker.checkType ctor.type)).bind (fun _ =>
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel) = .ok () at hconstructor
  cases hcheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel)
      (TypeChecker.checkType ctor.type) with
  | error err =>
    rw [hcheck] at hconstructor
    simp only [Except.bind] at hconstructor
    cases hconstructor
  | ok checked =>
    rw [hcheck] at hconstructor
    simpa only [bind, Except.bind] using hconstructor

end VerifyInductive
end Lean4Lean
