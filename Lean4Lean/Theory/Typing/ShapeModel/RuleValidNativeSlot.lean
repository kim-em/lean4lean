import Lean4Lean.Theory.Typing.ShapeModel.RuleValidInstSyntax

/-!
# The family slot of a native recursor

The restored owner family applied to the parameter variables and index variables (the major
domain of a native recursor type) is either a source family applied to the parameter variables,
or the container family of the slot's auxiliary specialization applied to the specialized
container parameters (`CompilationData.familyApp_cases`). The major of a restored equation of a
constructor of the same owner has the same form with the constructor (`major_cases`), so the
prefixes of parameter expressions of the two have the same length.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

theorem CompilationData.familyApp_cases {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CompilationData base src exp s g aux block)
    (o : Fin s.families.size) {e m : Nat} {out : VExpr}
    (h : (compilationRestoration src aux).expr
      (g.familyApp o (vars s.params.length (e + m)) (vars m 0)) = some out) :
    (∃ F ∈ src.types, src.types[o.val]? = some F ∧
      out = VExpr.mkApps (.const F.name g.levels) (vars s.params.length (e + m) ++ vars m 0)) ∨
    (∃ a ∈ aux, src.types.length ≤ o.val ∧ aux[o.val - src.types.length]? = some a ∧
      out = VExpr.mkApps (.const a.source.name (a.levels.map (·.inst g.levels)))
        (a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
          (vars s.params.length (e + m))) ++ vars m 0)) := by
  let r := compilationRestoration src aux
  have hparams : ∀ h ∈ r.heads, h.nparams = s.params.length := by
    intro h hh
    rw [compilationRestoration_nparams h hh, ← hdata.nparams, ← hdata.model.nparams]
  have hout := restored_ctorApp (e := e) hparams (by
    simpa only [Instance.familyApp, InductiveSignature.familyApp] using h)
  by_cases ho : o.val < src.types.length
  · obtain ⟨hname, -, -⟩ := CompilationData.source_slot hdata o ho
    have hF := List.getElem_mem (l := src.types) ho
    have hcn' : src.types[o.val].name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨_, hF, List.mem_cons_self⟩
    left
    refine ⟨_, hF, List.getElem?_eq_getElem ho, ?_⟩
    rcases hout with ⟨hnone, rfl⟩ | ⟨spec, hspec, hsome, _, _⟩
    · have hhn := hdata.headName_source hcn'
      unfold Restoration.headName at hhn
      rw [← hname, hnone] at hhn
      simp only at hhn
      rw [hhn, hname]
    · exfalso
      have : spec.auxiliary = src.types[o.val].name := by
        rw [← hname]; simpa using List.find?_some hsome
      exact hdata.source_head_disjoint hcn' (List.mem_map.mpr ⟨spec, hspec, this⟩)
  · right
    obtain ⟨envTypes, direct, _, hdirect, hlt, hrel⟩ := CompilationData.family_slot hdata o
    have ho' : src.types.length ≤ o.val := by omega
    rw [List.getElem_append_right ho'] at hrel
    have hrel' := List.mapM_eq_some.mp hdirect
    have hlen := Lean4Lean.List.Forall₂.length_eq hrel'
    have hlt2 : o.val < src.types.length + direct.length := by simpa using hlt
    have hjb : o.val - src.types.length < aux.length := by omega
    obtain ⟨_, hdf⟩ := forall₂_getElem_exists hrel' (o.val - src.types.length) hjb
    have ha := List.getElem_mem hjb
    have hname : s.families[o].name = aux[o.val - src.types.length].auxiliary := by
      have h1 := hrel.name
      rw [ContainerSpecialization.directFamily_name hdf] at h1
      exact h1
    refine ⟨_, ha, ho', List.getElem?_eq_getElem hjb, ?_⟩
    let a := aux[o.val - src.types.length]
    have hhead : HeadSpecialization.mk a.auxiliary src.uvars src.nparams a.source.name
        a.levels a.arguments ∈ r.heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    rcases hout with ⟨hnone, _⟩ | ⟨spec, hspec, hsome, _, rfl⟩
    · exfalso
      have := List.find?_eq_none.mp hnone _ hhead
      simp only [beq_iff_eq] at this
      exact this hname.symm
    · have hsa : spec.auxiliary = a.auxiliary := by
        rw [← hname]; simpa using List.find?_some hsome
      have := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1 hspec hhead hsa
      subst this
      rfl

theorem CompilationData.native_head {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CompilationData base src exp s g aux block)
    (o : Fin s.families.size) (args : List VExpr) :
    Restoration.expr.go (compilationRestoration src aux) (g.recursorHead .native o) args =
      some (VExpr.mkApps (.const ((compilationRestoration src aux).recursorName
        (g.recursorName o)) (VLevel.params g.uvars)) args) := by
  have hnone : (compilationRestoration src aux).heads.find?
      (fun h => h.auxiliary == g.recursorName o) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using hdata.heads_not_recursors o spec hs
  simp only [Instance.recursorHead, Restoration.expr.go, hnone]

/-- The syntax of a restored native equation and of the type of its recursor, with the major and
the major domain decomposed along the family slot of the owner. -/
theorem CompilationData.native_syntax {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CompilationData base src exp s g aux block)
    (j : Fin s.constructors.size) {df : VDefEq}
    (hg : (compilationRestoration src aux).equation (g.equation j) = some df) {Th0 : VExpr}
    (hTh0 : (compilationRestoration src aux).expr (g.recursorType s.constructors[j].owner) =
      some Th0) :
    ∃ (Ds idx : List VExpr) (R : VExpr) (Es doms₀ : List VExpr) (TbH : VExpr) (c : Name)
      (lv : List VLevel) (ps : List VExpr) (Fn : Name) (lvF : List VLevel) (pargs : List VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps
        (.const ((compilationRestoration src aux).recursorName
          (g.recursorName s.constructors[j].owner)) (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[j].fields.length ++ idx ++
          [VExpr.mkApps (.const c lv) (ps ++ vars s.constructors[j].fields.length 0)])) ∧
      df.rhs = VExpr.wrapLams Ds R ∧
      df.type = VExpr.wrapForalls Ds (VExpr.mkApps
        (.bvar (s.constructors[j].fields.length + s.constructors.size +
          (s.families.size - 1 - s.constructors[j].owner.val)))
        (idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars s.constructors[j].fields.length 0)])) ∧
      Ds.length = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[j].fields.length ∧
      idx.length = s.families[s.constructors[j].owner].indices.length ∧
      (∃ hm : s.params.length + s.constructors[j].owner.val < Ds.length,
        Ds[s.params.length + s.constructors[j].owner.val] =
          VExpr.wrapForalls Es (.sort g.targetLevel)) ∧
      Es.length = s.families[s.constructors[j].owner].indices.length + 1 ∧
      Th0 = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const Fn lvF)
        (pargs ++ vars s.families[s.constructors[j].owner].indices.length 0)]) TbH ∧
      doms₀.length = s.params.length + (s.families.size + s.constructors.size) +
        s.families[s.constructors[j].owner].indices.length ∧
      ps.length = pargs.length ∧
      ((∃ F ∈ src.types, src.types[s.constructors[j].owner.val]? = some F ∧ Fn = F.name ∧
          lvF = g.levels ∧ lv = g.levels ∧ ∃ cv ∈ F.ctors, cv.name = c) ∨
        (∃ a ∈ aux, src.types.length ≤ s.constructors[j].owner.val ∧
          aux[s.constructors[j].owner.val - src.types.length]? = some a ∧ Fn = a.source.name ∧
          lvF = a.levels.map (·.inst g.levels) ∧ lv = a.levels.map (·.inst g.levels) ∧
          ∃ cv ∈ a.source.ctors, cv.name = c)) := by
  obtain ⟨Ds, idx, major, R, Es, hl, hr, ht, hDs, hidx, hmaj, hmot, hEs⟩ :=
    restored_equation_syntax g _ .native j hg (CompilationData.native_head hdata _)
  obtain ⟨Ds', idx', major', hl', -, hcases⟩ := CompilationData.major_cases hdata j hg
  have hinj := ruleBody_inj (hl.symm.trans hl')
  obtain ⟨-, -, hpre⟩ := mkApps_const_inj hinj.1
  have hidx' : idx = idx' := List.append_cancel_left hpre
  subst hidx'
  have hmm : major = major' := hinj.2
  subst hmm
  have hca : s.constructors[j].indices.length =
      s.families[s.constructors[j].owner].indices.length :=
    hdata.model.constructorArity _ (Array.getElem_mem_toList ..)
  obtain ⟨doms₀, TbH, majorDom, hTh, hdoms, hmd⟩ := restored_recursorType_syntax g _ _ hTh0
  rcases CompilationData.familyApp_cases hdata s.constructors[j].owner (e := s.families.size + s.constructors.size) hmd with
    ⟨F, hF, hFo, rfl⟩ | ⟨a, ha, hlo, hao, rfl⟩
  · rcases hcases with ⟨F', hF', hF'o, cv, hcv, hcn, rfl⟩ | ⟨a, -, hlo, hao, -⟩
    · rw [hFo] at hF'o; cases hF'o
      refine ⟨Ds, idx, R, Es, doms₀, TbH, _, _, _, _, _, _, hl, hr, ht, hDs, hidx.trans hca, hmot,
        hEs, hTh, hdoms, by simp [vars_length'], .inl ⟨F, hF, hFo, rfl, rfl, rfl, cv, hcv, rfl⟩⟩
    · exfalso
      have := List.getElem?_eq_none_iff.mpr hlo
      rw [this] at hFo; cases hFo
  · rcases hcases with ⟨F', hF', hF'o, -⟩ | ⟨a', ha', hlo', hao', cv, hcv, hcn, rfl⟩
    · exfalso
      have := List.getElem?_eq_none_iff.mpr hlo
      rw [this] at hF'o; cases hF'o
    · rw [hao] at hao'; cases hao'
      refine ⟨Ds, idx, R, Es, doms₀, TbH, _, _, _, _, _, _, hl, hr, ht, hDs, hidx.trans hca, hmot,
        hEs, hTh, hdoms, by simp, .inr ⟨a, ha, hlo, hao, rfl, rfl, rfl, cv, hcv, rfl⟩⟩

end Lean4Lean.ShapeModel
