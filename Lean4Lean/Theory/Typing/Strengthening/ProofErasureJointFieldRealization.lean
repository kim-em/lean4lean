import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Common typed realizations of recursively checked structure fields

Source reflection supplies equality of the majors before substitution. Typed
expansion and projection computation then supply actual common typings for
each retained field, without an inverse substitution or weakening principle.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Every projection appearing in a typed structure expansion has a typing.
This also covers dependent field types without selecting a closed recipe. -/
theorem structure_expansion_projection_typed
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (structExpand family info ls ps a) T)
    (hi : i < info.numFields) : VExpr.WF env univs Γ (.proj family i a) := by
  apply (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Equal majors have projections at a common type whenever the left expansion
is typed. This supplies local realizations for carrier-field substitution. -/
theorem structure_equal_projection_typings
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A)
    (ht : env.HasType univs Γ (structExpand family info ls ps a) T)
    (hi : i < info.numFields) :
    ∃ F, env.HasType univs Γ (.proj family i a) F ∧ env.HasType univs Γ (.proj family i b) F := by
  obtain ⟨F, ha⟩ := structure_expansion_projection_typed hΓ ht hi
  have HP := SimAt.proj henv.orderedStrong hΓ
    (fun _ hx => (show env.IsDefEqU univs Γ a b from ⟨_, H⟩).of_l henv hΓ hx) F ha
  exact ⟨F, ha, HP.hasType.2⟩

/-- A constructor field and the corresponding projection of an equal major
have actual common typings. The returned field has the exact requested raw
erasure, so it can be used by a typed recursive transport hypothesis. -/
theorem proofErase_equal_structure_field_realize
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ e m T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ee : proofErase Γ e = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (hj : i < fields.length) :
    ∃ a A, env.HasType univs Γ a A ∧ env.HasType univs Γ (.proj family i m) A ∧
      proofErase Γ a = fields[i] := by
  obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ee
  let ps₀ := args.take info.nparams
  let fs₀ := args.drop info.nparams
  have Hps : ps₀.map (proofErase Γ) = ps := by
    simp only [ps₀, List.map_take, ← Hargs, ← hp, List.take_left]
  have Hfs : fs₀.map (proofErase Γ) = fields := by
    simp only [fs₀, List.map_drop, ← Hargs, ← hp, List.drop_left]
  have hps : ps₀.length = info.nparams := by
    simpa only [List.length_map, hp] using congrArg List.length Hps
  have hfs : fs₀.length = info.numFields := by
    simpa only [List.length_map, hf] using congrArg List.length Hfs
  have Hsplit : args = ps₀ ++ fs₀ := (List.take_append_drop info.nparams args).symm
  have hlen : args.length = info.nparams + info.numFields := by rw [Hsplit]; simp [hps, hfs]
  have hnat := structure_constructor_family hΓ hi hx hlen H.hasType.1
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
    (show (args.take info.nparams).length = info.nparams from hps) hx hnat).2 hadm
  obtain ⟨A, hproj, hm⟩ := structure_equal_projection_typings hΓ H hexp (by omega : i < info.numFields)
  have hif : i < fs₀.length := by omega
  have hget : args[info.nparams + i]? = some fs₀[i] := by
    rw [Hsplit, List.getElem?_append_right (by omega)]
    simp only [hps, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hif]
  exact ⟨fs₀[i], A, HasType.projIota_field hΓ hi hproj hlen hget, hm,
    by simp only [← Hfs, List.getElem_map]⟩

end Lean4Lean.VEnv.Strengthening
