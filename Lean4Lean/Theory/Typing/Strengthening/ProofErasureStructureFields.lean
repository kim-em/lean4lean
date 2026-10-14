import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureEta

/-! # Source-typed structure eta with recursive field premises

The source constructor determines the family parameters below insertion.
Dependent spine comparison aligns field types before invoking each field premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Common-typed field comparisons suffice for constructor eta once the exact
projected expansion is typed. Field types are aligned sequentially along the spine. -/
theorem structure_spine_recursive_fields (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hps : ps.length = info.nparams)
    (hx : info.nindices = 0) (hf : fields.length = info.numFields)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (he : env.HasType univs Γ (mkApps (.const info.ctorName ls) (ps ++ fields))
      (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps))
    (H : ∀ i (h : i < fields.length) T, env.HasType univs Γ fields[i] T →
      env.HasType univs Γ (.proj family i m) T → env.IsDefEqU univs Γ fields[i] (.proj family i m)) :
    env.IsDefEqU univs Γ (mkApps (.const info.ctorName ls) (ps ++ fields)) m := by
  have hfields : List.Forall₂ (fun a b => ∀ T, env.HasType univs Γ a T →
      env.HasType univs Γ b T → env.IsDefEqU univs Γ a b)
      fields ((List.range info.numFields).map (fun i => .proj family i m)) := by
    apply Lean4Lean.List.forall₂_of_getElem (by simp [hf])
    intro i hj hj' T ha hb
    simp only [List.getElem_map, List.getElem_range] at hb ⊢
    exact H i hj T ha hb
  have hparams : List.Forall₂ (fun a b => ∀ T, env.HasType univs Γ a T →
      env.HasType univs Γ b T → env.IsDefEqU univs Γ a b) ps ps :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ _ ht _ => ⟨_, ht⟩)
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, he⟩
  have HC := mkApps_common_arguments hΓ (hparams.append' hfields) ⟨_, hhead⟩ ⟨_, he⟩ ⟨_, hexp⟩
  exact HC.trans henv hΓ ⟨_, IsDefEq.structEta hi hps hx hm hexp⟩

/-- A lifted constructor shape and common endpoint typing reconstruct the
canonical family and projected expansion below insertion. Only the recursive
field comparisons remain as premises; no lower bridge typing is assumed. -/
theorem proofErase_structure_fields_reflect (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hm : env.HasType univs Γ m T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ee : (proofErase Γ e).liftN n k = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (H : ∀ i (h : i < fields.length) {a A}, env.HasType univs Γ a A →
      env.HasType univs Γ (.proj family i m) A →
      (proofErase Γ a).liftN n k = fields[i] → env.IsDefEqU univs Γ a (.proj family i m)) :
    env.IsDefEq univs Γ e m T := by
  obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Ee
  obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Es
  rw [Hargs] at Eargs
  simp only [List.map_map, Function.comp_def] at Eargs
  let ps₀ := args.take info.nparams
  let fs₀ := args.drop info.nparams
  have Hps : ps₀.map (fun a => (proofErase Γ a).liftN n k) = ps := by
    simp only [ps₀, List.map_take, ← Eargs, ← hp, List.take_left]
  have Hfs : fs₀.map (fun a => (proofErase Γ a).liftN n k) = fields := by
    simp only [fs₀, List.map_drop, ← Eargs, ← hp, List.drop_left]
  have hps : ps₀.length = info.nparams := by simpa only [List.length_map, hp] using congrArg List.length Hps
  have hfs : fs₀.length = info.numFields := by simpa only [List.length_map, hf] using congrArg List.length Hfs
  have Hsplit : args = ps₀ ++ fs₀ := (List.take_append_drop info.nparams args).symm
  rw [Hsplit] at he ⊢
  have hnat := structure_constructor_family hΓ hi hx (by simp [hps, hfs]) he
  rw [List.take_left' hps] at hnat
  have hm' := hm.defeqU_r henv hΓ (he.uniqU henv hΓ hnat)
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hps hx hm').2 hadm
  have HH := structure_spine_recursive_fields hΓ hi hps hx hfs hm' hnat hexp (by
    intro i hj A ha hb
    have hj' : i < fields.length := by omega
    apply H i hj' ha hb
    simp only [← Hfs, List.getElem_map])
  exact HH.of_l henv hΓ he

end Lean4Lean.VEnv.Strengthening
