import Lean4Lean.Verify.Inductive.Recursor.Entries.AddConstants

/-! Exact lookup and mutual-block effects of a lockstep installation (`AddConstants`), as the
recursor phase uses them. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

theorem AddConstants.entryNames
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hentry : entry ∈ entries) : entry.1.name = entry.2.name := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact htr.2
    · exact ih htail

/-- A lockstep installation consisting only of constructors, recursors, or
other non-inductive constants preserves closure of all mutual blocks. -/
theorem AddConstants.closesMutuals
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env)
    (hnind : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
      ∀ (value : InductiveVal),
      entry.1 ≠ ConstantInfo.inductInfo value) :
    MutualInductivesClosed outEnv := by
  induction H with
  | nil => exact hclosed
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn _ _ _ _ _ Htail ih =>
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (env.add ci).constants.WF := by
      change (env.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    have hclosedNext : MutualInductivesClosed (env.add ci) := by
      change MutualInductivesClosed
        (Lean4Lean.AddInductive.addConstant env ci)
      exact hclosed.addNonInductive hwf hn
        (fun value => hnind (ci, ci') (by simp) value)
    exact ih hnextWF hclosedNext fun entry hentry value =>
      hnind entry (by simp [hentry]) value



theorem GeneratedRecursors.closesMutuals
    (H : GeneratedRecursors safety sourceEnv lparams elimLevel c stats
      indTypes recInfos entries)
    (Hinstalled : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env) :
    MutualInductivesClosed outEnv := by
  apply Hinstalled.closesMutuals hwf hclosed
  intro entry hmem inductiveValue
  rcases entry with ⟨info, value⟩
  exact H.nonInductive info value hmem inductiveValue

end VerifyInductive
end Lean4Lean
