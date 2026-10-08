import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem AddConstants.valueNonprimitive
    (H : AddConstants safety prodEnv venv entries outProdEnv outVEnv)
    (hvalue : value ∈ entries.map Prod.snd) :
    ¬ Kernel.Environment.primitives.contains value.name := by
  induction H with
  | nil => simp at hvalue
  | cons hn hnprim htr hwf hadd hdelta Htail ih =>
    simp only [List.map_cons, List.mem_cons] at hvalue
    rcases hvalue with hhead | htail
    · subst value
      simpa [htr.2] using hnprim
    · exact ih htail

end VerifyInductive
end Lean4Lean
