import Lean4Lean.Theory.Typing.Strengthening.StructureUnfoldingSupply

/-! # Projection certificates with proof fields

The two-parameter, two-proof-field telescope of conjunction satisfies the new
certificate at every universe instance. This establishes the field condition
syntactically, without assuming a typing for a reconstructed constructor.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- A conjunction-shaped constructor has two proof-valued fields. Its result
and source universe need not be inspected to establish projection admissibility. -/
theorem ProofFields.conjunction_shape
    (hshape : info.ctorType = wrapForalls [.sort .zero, .sort .zero, .bvar 1, .bvar 1] result)
    (hp : info.nparams = 2) (hf : info.numFields = 2) :
    ProofFields env U info levels := by
  apply ProofFields.of_telescope hshape (by simp [hp, hf])
  intro j hj hparam
  have hjcases : j = 2 ∨ j = 3 := by simp only [List.length_cons, List.length_nil] at hj; omega
  rcases hjcases with rfl | rfl
  · simp only [List.map_cons, List.map_nil, instL, VLevel.inst, List.take_succ_cons,
      List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
    exact .bvar (.succ .zero)
  · simp only [List.map_cons, List.map_nil, instL, VLevel.inst, List.take_succ_cons,
      List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
    exact .bvar (.succ .zero)

end Lean4Lean.VEnv.Strengthening.StructureReplay
