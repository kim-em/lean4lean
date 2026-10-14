import Lean4Lean.Theory.Typing.Strengthening.StructureEtaParameterReduction

/-! # Typed changes of saturated constructor parameters

Structure eta followed by its projections can change displayed parameters and
universe syntax while retaining every field. This rule records precisely that
conversion. It is not arbitrary conversion of constructor arguments and is not
yet a terminal calculus closed under every expression constructor.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- The intrinsic family of an unindexed saturated constructor is obtained from
its displayed parameters, with no hidden result indices. -/
theorem constructor_unindexed_family (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : params.length = info.nparams) (hf : fields.length = info.numFields)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) (params ++ fields)) T) :
    env.IsDefEqU univs Γ T (mkApps (.const family levels) params) := by
  obtain ⟨idx, H⟩ := ht.ctorApp_type hΓ hi (by simp [hp, hf])
  simp only [← hp, List.take_left] at H
  obtain ⟨u, hT⟩ := ht.isType henv hΓ
  have hF := hT.defeqU_l henv hΓ H
  have hn := StructureReplay.family_arity henv hΓ hi ⟨u, hF⟩
  have hz : idx.length = 0 := by simp only [List.length_append, hp, hx] at hn; omega
  cases List.length_eq_zero_iff.1 hz
  simpa only [List.append_nil] using H

/-- A saturated unindexed constructor may change only its parameter prefix and
universes, keeping all fields literally equal. Both endpoints have a common
type, and projection admissibility is retained at the right universe instance. -/
inductive ConstructorParameterChange : List VExpr → VExpr → VExpr → Prop where
  | intro : env.projections family info → info.nindices = 0 →
      params.length = info.nparams → params'.length = info.nparams →
      fields.length = info.numFields →
      ((info.resultLevel.inst levels').IsNeverZero ∨ StructureReplay.ProofFields env univs info levels') →
      env.HasType univs Γ (mkApps (.const info.ctorName levels) (params ++ fields)) T →
      env.HasType univs Γ (mkApps (.const info.ctorName levels') (params' ++ fields)) T →
      ConstructorParameterChange Γ (mkApps (.const info.ctorName levels) (params ++ fields))
        (mkApps (.const info.ctorName levels') (params' ++ fields))

/-- The rule is realized by one actual structure eta root followed by its
field projections. It adds no new definitional equation to the calculus. -/
theorem ConstructorParameterChange.full (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorParameterChange Γ a b) : FullReduction Γ a b := by
  cases H with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz ht ht' =>
    have hTF := constructor_unindexed_family hΓ hi hx hp' hf ht'
    have hm := ht.defeqU_r henv hΓ hTF
    have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hp' hx hm).2 hz
    have RE : FullReduction Γ _ (structExpand family info levels' params' _) :=
      .tail .rfl (.structEta hi hp' hx hm hc)
    have HR : List.Forall₂ (FullReduction Γ)
        ((List.range info.numFields).map (fun i => .proj family i
          (mkApps (.const info.ctorName levels) (params ++ fields)))) fields := by
      apply List.forall₂_of_getElem (by simp [hf])
      intro i hiP hiF
      simp only [List.getElem_map, List.getElem_range]
      have hiN : i < info.numFields := by simpa using hiP
      have hg : (params ++ fields)[info.nparams + i]? = some fields[i] := by
        rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem hiF
      obtain ⟨F, hproj⟩ := mkApps_arg_type hΓ hc (arg := .proj family i _) (by
        apply List.mem_append_right
        exact List.mem_map.2 ⟨i, List.mem_range.2 hiN, rfl⟩)
      exact .tail .rfl (.projIota hi hproj hg
        (HasType.projIota_field hΓ hi hproj (by simp [hp, hf]) hg))
    exact RE.trans (FullReduction.mkApps .rfl ((FullReduction.forall₂_rfl params').append' HR))

/-- Every independent source typing is preserved by the derived conversion. -/
theorem ConstructorParameterChange.simAt (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorParameterChange Γ a b) : env.SimAt univs Γ a b :=
  fun _ ht => H.full hΓ |>.defeq hΓ ht

/-- A parameter change cannot occur at a sort or function type. This keeps the
new root separate from the type heads used by strengthening's head repair. -/
theorem ConstructorParameterChange.not_sort_or_pi (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorParameterChange Γ a b)
    (ht : (∃ u, env.HasType univs Γ a (.sort u)) ∨
      ∃ A B, env.HasType univs Γ a (.forallE A B)) : False := by
  cases H with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz ha hb =>
    have hm := ha.defeqU_r henv hΓ (constructor_unindexed_family hΓ hi hx hp' hf hb)
    exact structure_source_not_sort_or_pi hΓ hi hm ht

/-- The root relation is symmetric. Universe conversion also transports the
closed proof-field certificate when admissibility comes from proof fields. -/
theorem ConstructorParameterChange.symm (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorParameterChange Γ a b) : ConstructorParameterChange Γ b a := by
  cases H with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz ha hb =>
    have hm := ha.defeqU_r henv hΓ (constructor_unindexed_family hΓ hi hx hp' hf hb)
    obtain ⟨hw, hl, hw', he⟩ := StructureReplay.constructor_levels henv hΓ hi (by simp [hp, hf]) hm
    have he' := he.flip.imp (fun _ _ h => h.symm)
    have hz' : (info.resultLevel.inst levels).IsNeverZero ∨ StructureReplay.ProofFields env univs info levels := by
      rcases hz with hz | hz
      · exact .inl (hz.of_equiv (VLevel.inst_congr rfl he'))
      · exact .inr (hz.level_congr henv hi hw' hw (he.length_eq.symm.trans hl) he')
    exact .intro hi hx hp' hp hf hz' hb ha

/-- Finite computation after a root parameter change can be moved before it.
The left computes exactly the same fields; the right's new parameter prefix
is retained by one residual parameter change. No parameter phases are needed. -/
theorem ConstructorParameterChange.compute (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hn : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (H : ConstructorParameterChange Γ a b) (R : PrefixCompute D Γ b c) :
    ∃ a', PrefixCompute D Γ a a' ∧ ConstructorParameterChange Γ a' c := by
  cases H with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz ha hb =>
    obtain ⟨args, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi) (hn hi)
    have hlen : args.length = info.nparams + info.numFields := by simpa [hp', hf] using HA.length_eq.symm
    have hpc : (args.take info.nparams).length = info.nparams := by simp [hlen]
    have hfc : (args.drop info.nparams).length = info.numFields := by simp [hlen]
    have HF := List.forall₂_drop HA info.nparams
    rw [← hp', List.drop_left, hp'] at HF
    have RL : PrefixCompute D Γ _ (mkApps (.const info.ctorName levels) (params ++ args.drop info.nparams)) :=
      .mkApps_paths .refl ((List.Forall₂.rfl (fun _ _ => PrefixCompute.refl)).append' HF)
    refine ⟨_, RL, ?_⟩
    have HR : ConstructorParameterChange Γ _
        (mkApps (.const info.ctorName levels') (args.take info.nparams ++ args.drop info.nparams)) :=
      .intro hi hx hp hpc hfc hz (RL.simAt hs hΓ _ ha).hasType.2
        (by simpa only [List.take_append_drop] using (R.simAt hs hΓ _ hb).hasType.2)
    simpa only [List.take_append_drop] using HR

end Lean4Lean.VEnv.Strengthening.PureObservation
