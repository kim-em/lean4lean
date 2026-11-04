import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaReplay

/-! # Projection residuals for the staged masked structure language

The new structure primitive introduces constructor spines. Their projection
redexes cancel to the original field erasure, including proof fields. This
critical pair requires no new native recovery for the expanded major or fields.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A constructor projection selects the static field mask directly, with no
native recovery premise for any parameter or field. -/
theorem ProofShape.nativeStructureOutput_projection
    (hi : env.projections s info) (hp : ps.length = info.nparams) (hj : j < info.numFields) :
    Compute (Primitive D) (.proj s j (nativeStructureOutput s info ls ps m))
      (nativeStructureField s info ls m j) := by
  apply Compute.base
  apply Primitive.projIota hi
  · simp only [List.length_append, List.length_map, List.length_range, hp]
  · rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]

/-- Actual typing identifies the selected static mask with the original field's
erasure. This is a core computation, including for dependent proof fields. -/
theorem proofErase_static_structure_projection_residual
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hj : j < info.numFields)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) T)
    (hn : ¬ IsProof Γ (structExpand s info ls ps m)) :
    Compute (Primitive D) (.proj s j (proofErase Γ (structExpand s info ls ps m)))
      (proofErase Γ (.proj s j m)) := by
  classical
  rw [proofErase_nativeStructureOutput hΓ hi hp hc hn]
  have E : proofErase Γ (.proj s j m) = nativeStructureField s info ls (proofErase Γ m) j := by
    unfold nativeStructureField
    have H := structure_proofField_iff hΓ hi hp hj hc
    by_cases h : StructureReplay.ProofField env univs info ls j
    · rw [if_pos h, proofErase_eq_proof.2 (H.1 h)]
    · rw [if_neg h]
      exact if_neg (fun h' => h (H.2 h'))
  rw [E]
  exact nativeStructureOutput_projection hi (by simpa only [List.length_map] using hp) hj

end Lean4Lean.VEnv.Strengthening
