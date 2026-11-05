import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionRecipeComputation

/-! # Dependent recipe paths from actual projection typing

A retained projection forces a never-zero major universe at every recovered
family assignment. Registration supplies the constructor prefix substitution,
so the general recipe-path theorem needs no external telescope certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Any selected major family of a retained projection has well-formed levels,
the registered arity, and a never-zero result universe. No native recovery or
computational type-completeness assumption is involved. -/
theorem retained_projection_family_facts
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args)) :
    (∀ l ∈ ls, l.WF univs) ∧ ls.length = info.uvars ∧
      args.length = info.nparams + info.nindices ∧ (info.resultLevel.inst ls).IsNeverZero := by
  obtain ⟨info₀, ls₀, ps₀, idx₀, sm₀, F₀, u₀, hi₀, hw₀, hl₀, hp₀, hiLen₀,
    hfield₀, hF₀, hm₀, hclosed, hguard⟩ := ht.proj_inv henv hΓ
  obtain rfl := henv.ordered.projections_unique hi₀ hi
  obtain ⟨_, hfamily₀⟩ := hm₀.hasType.2.isType henv hΓ
  obtain ⟨hls, hargs⟩ := (hm₀.hasType.2.uniqU henv hΓ hm).rigidApp_inv
    henv hΓ (henv.projectionRigid hi₀) hfamily₀
  have hlevels : ls.length = info₀.uvars := hls.length_eq.symm.trans hl₀
  have hnz₀ : (info₀.resultLevel.inst ls₀).IsNeverZero := by
    rcases hguard with hguard | hguard
    · exact hguard
    · have hpj : env.HasType univs Γ (.proj s j m) F₀ :=
        .projDF hi₀ hw₀ hl₀ hp₀ hiLen₀ hfield₀ hF₀ hm₀ hm₀ hclosed (.inr hguard)
      have hFprop : env.HasType univs Γ F₀ (.sort .zero) :=
        (IsDefEq.sortDF (hF₀.sort_r henv hΓ) (by trivial) hguard).defeq hF₀
      exact (hn ⟨F₀, hpj, hFprop⟩).elim
  obtain ⟨_, hfamily⟩ := hm.isType henv hΓ
  obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const s ls) args) from
    ⟨_, hfamily⟩).of_mkApps henv hΓ
  obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ hhead
  exact ⟨hw, hlevels, StructureReplay.family_arity henv hΓ hi₀ ⟨_, hfamily⟩,
    hnz₀.of_equiv (VLevel.inst_congr (by rfl) hls)⟩

/-- The complete dependent field recipe follows any major computation from
an actual retained projection. The source family can be indexed. All parameter
and preceding-field typing is derived here, and the target remains arbitrary raw
syntax. This supplies a residual path, not confluence for its conversion tails. -/
theorem typed_projectionType_compute_major
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m))
      (projectionType s info doms j hj (args.map (proofErase Γ)) out) := by
  obtain ⟨hw, hl, hargs, hnz⟩ := retained_projection_family_facts hΓ hi ht hn hm
  have hp : (args.take info.nparams).length = info.nparams := by simp; omega
  have hidx : (args.drop info.nparams).length = info.nindices := by simp; omega
  have hm' : env.HasType univs Γ m (VExpr.mkApps (.const s ls)
      (args.take info.nparams ++ args.drop info.nparams)) := by simpa only [List.take_append_drop] using hm
  obtain ⟨tail, hps⟩ := projection_parameters_typed henv hΓ hi hp hm'
  have W := projection_prefix_subst hΓ hi hw hl hnz HT hps hp hidx hm' (Nat.le_of_lt hj)
  rw [projection_argSubst_eq_ofList] at W
  obtain ⟨_, hF⟩ := HT.doms _ hj
  have HC := proofErase_projection_template_compute_major_of_subst
    (fun {Δ Δ' a b τ} ⟨stage, H⟩ WR =>
      ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage H WR⟩)
    hΓ hF W (by simp only [List.length_append, projsOf, List.length_map, List.length_range,
      hp, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]) R
  simpa only [projectionType, List.map_take] using HC

end Lean4Lean.VEnv.Strengthening
