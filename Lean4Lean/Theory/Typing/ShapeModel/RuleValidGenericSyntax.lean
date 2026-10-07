import Lean4Lean.Theory.Typing.ShapeModel.RuleValidGenericSem

/-!
# Syntax of generic eliminator equations and of generic eliminator types

`generic_syntax`: a generic equation of a certified schema is a lambda telescope `Ds` over the
eliminator applied to the prefix variables, the restored indices and a constructor major; its
type is the Pi telescope over `Ds` of the motive applied to the indices and the major; the
generic eliminator type is a Pi telescope ending in the restored owner family applied to
parameter expressions and the index variables; the major and the major domain are decomposed
along the family slot of the owner.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

theorem ruleBody_eq {Ds Ds' : List VExpr} {hd : VExpr} (hhd : hd.getAppFnArgs = (hd, []))
    (hlam : ∀ d b, hd ≠ .lam d b) {xs xs' : List VExpr} {m m' : VExpr}
    (heq : VExpr.wrapLams Ds (VExpr.mkApps hd (xs ++ [m])) =
      VExpr.wrapLams Ds' (VExpr.mkApps hd (xs' ++ [m']))) :
    Ds = Ds' ∧ xs = xs' ∧ m = m' := by
  have h1 := congrArg lamDoms heq
  rw [lamDoms_wrapLams (mkApps_ne_lam hlam _), lamDoms_wrapLams (mkApps_ne_lam hlam _)] at h1
  have h2 := congrArg VExpr.stripLams heq
  rw [stripLams_wrapLams', stripLams_wrapLams', mkApps_snoc, mkApps_snoc] at h2
  have h3 := VExpr.app.inj h2
  have h4 := congrArg VExpr.getAppFnArgs h3.1
  rw [spine_mkApps_exact _ _ hhd, spine_mkApps_exact _ _ hhd] at h4
  exact ⟨h1, (Prod.mk.inj h4).2, h3.2⟩

theorem view_families_getElem {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (k : Fin (schema.view owner).families.size) :
    (schema.view owner).families[k] = schema.signature.families[owner] := by
  obtain ⟨k, hk⟩ := k
  simp only [CaseSchema.view_familyCount] at hk
  obtain rfl : k = 0 := by omega
  rfl

theorem view_params {schema : CaseSchema} {owner : Fin schema.signature.families.size} :
    (schema.view owner).params = schema.signature.params := rfl

theorem generic_syntax {base : VEnv} {source expanded : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} {key : Name} {g0 : Instance schema.signature}
    {aux : List ContainerSpecialization}
    (hdata : CompilationData base source expanded schema.signature g0 aux block)
    (hprior : CertifiedSpecializations base aux)
    (hr : schema.restoration = compilationRestoration source aux)
    (hnames : schema.originalFamilies = source.types.map (·.name))
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {df : VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules) {Th0 : VExpr}
    (hT0 : schema.genericType owner = some Th0) :
    ∃ (nf Cv : Nat) (Ds idx : List VExpr) (R : VExpr) (Es doms₀ : List VExpr) (TbH : VExpr)
      (c : Name) (lv : List VLevel) (ps : List VExpr) (Fn : Name) (lvF : List VLevel)
      (pargs : List VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps (.elim key owner.val (.param 0 :: schema.genericLevels))
        (vars (schema.signature.params.length + (1 + Cv)) nf ++ idx ++
          [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])) ∧
      df.rhs = VExpr.wrapLams Ds R ∧
      df.type = VExpr.wrapForalls Ds (VExpr.mkApps (.bvar (nf + Cv))
        (idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])) ∧
      Ds.length = schema.signature.params.length + (1 + Cv) + nf ∧
      idx.length = schema.signature.families[owner].indices.length ∧
      (∃ hm : schema.signature.params.length < Ds.length,
        Ds[schema.signature.params.length] = VExpr.wrapForalls Es (.sort (.param 0))) ∧
      Es.length = schema.signature.families[owner].indices.length + 1 ∧
      Th0 = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const Fn lvF)
        (pargs ++ vars schema.signature.families[owner].indices.length 0)]) TbH ∧
      doms₀.length = schema.signature.params.length + (1 + Cv) +
        schema.signature.families[owner].indices.length ∧
      ps.length = pargs.length ∧
      ((∃ F ∈ source.types, source.types[owner.val]? = some F ∧ Fn = F.name ∧
          lvF = schema.genericLevels ∧ lv = schema.genericLevels ∧ ∃ cv ∈ F.ctors, cv.name = c) ∨
        (∃ a ∈ aux, source.types.length ≤ owner.val ∧
          aux[owner.val - source.types.length]? = some a ∧ Fn = a.source.name ∧
          lvF = a.levels.map (·.inst schema.genericLevels) ∧
          lv = a.levels.map (·.inst schema.genericLevels) ∧
          ∃ cv ∈ a.source.ctors, cv.name = c)) := by
  obtain ⟨index, hrestore⟩ := CaseSchema.equation_origin hgen hdf
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [CaseSchema.view_familyCount] at this
    omega
  have hhd : ∀ args, Restoration.expr.go schema.restoration
      (g.recursorHead (.abstract key owner.val) (schema.view owner).constructors[index].owner) args =
      some (VExpr.mkApps (.elim key owner.val (.param 0 :: schema.genericLevels)) args) := by
    intro args
    simp only [Instance.recursorHead, hzero, Nat.add_zero, Restoration.expr.go]
    rfl
  obtain ⟨Ds, idx, major, R, Es, hl, hrr, ht, hDs, hidx, -, hmot, hEs, -, -⟩ :=
    restored_equation_syntax g _ _ index hrestore hhd
  obtain ⟨index', Ds', idx', c, lv, ps, hl', -, hDs', -, hidx2, j, hjo, hjf, e, he, hres⟩ :=
    Certified.generic_shape ⟨expanded, g0, aux, hdata, hprior, hr, hnames⟩ hgen hdf
  obtain ⟨hDsEq, hpre, hmaj⟩ := ruleBody_eq (hd := .elim key owner.val
    (.param 0 :: schema.genericLevels)) rfl (by intros; simp) (hl.symm.trans hl')
  subst hDsEq
  have hnf : (schema.view owner).constructors[index].fields.length =
      (schema.view owner).constructors[index'].fields.length := by
    have h1 : Ds.length = schema.signature.params.length + (1 + (schema.view owner).constructors.size) +
        (schema.view owner).constructors[index].fields.length := hDs
    rw [hDs'] at h1
    omega
  rw [hnf] at hpre
  have hidxEq : idx = idx' := List.append_cancel_left hpre
  subst hidxEq hmaj
  -- the generic eliminator type
  have hT0' : schema.restoration.expr (g.recursorType (schema.viewOwner owner)) = some Th0 := hT0
  obtain ⟨doms₀, TbH, majorDom, hTh, hdoms, hmd⟩ := restored_recursorType_syntax g _ _ hT0'
  have hdoms' : doms₀.length = schema.signature.params.length +
      (1 + (schema.view owner).constructors.size) +
      schema.signature.families[owner].indices.length := hdoms
  rw [hr] at hmd hres
  have hmd' : (compilationRestoration source aux).expr (VExpr.mkApps
      (.const schema.signature.families[owner].name schema.genericLevels)
      (vars schema.signature.params.length ((1 + (schema.view owner).constructors.size) +
        schema.signature.families[owner].indices.length) ++
        vars schema.signature.families[owner].indices.length 0)) = some majorDom := hmd
  have hjnf : schema.signature.constructors[j].fields.length =
      (schema.view owner).constructors[index'].fields.length := hjf
  have htype : df.type = VExpr.wrapForalls Ds (VExpr.mkApps
      (.bvar ((schema.view owner).constructors[index'].fields.length +
        (schema.view owner).constructors.size)) (idx ++
          [VExpr.mkApps (.const c lv) (ps ++ vars (schema.view owner).constructors[index'].fields.length 0)])) := by
    rw [ht, hzero, ← hnf]; rfl
  obtain ⟨hm, hmot'⟩ := hmot
  have hmot'' : ∃ hm : schema.signature.params.length < Ds.length,
      Ds[schema.signature.params.length] = VExpr.wrapForalls Es (.sort (.param 0)) := by
    simp only [hzero, Nat.add_zero] at hm hmot'
    exact ⟨hm, hmot'⟩
  have hEs' : Es.length = schema.signature.families[owner].indices.length + 1 := by
    rw [hEs, view_families_getElem]
  rcases CompilationData.familyHead_cases hdata owner (G := schema.genericLevels)
      (e := 1 + (schema.view owner).constructors.size)
      (m := schema.signature.families[owner].indices.length) hmd' with
    ⟨F, hF, hFo, rfl⟩ | ⟨a, ha, hlo, hao, rfl⟩
  · rcases CompilationData.ctorApp_cases hdata j hres with
      ⟨F', hF', hF'o, cv, hcv, hcn, hm2⟩ | ⟨a, -, hlo, -, -⟩
    · obtain ⟨rfl, rfl, hps⟩ := mkApps_const_inj hm2
      rw [hjnf] at hps
      have hps' := List.append_cancel_right hps
      rw [hjo] at hF'o
      rw [hFo] at hF'o; cases hF'o
      refine ⟨_, _, Ds, idx, R, Es, doms₀, TbH, _, _, _, _, _, _, hl', ?_, htype, ?_, hidx2,
        hmot'', hEs', hTh, hdoms', ?_, .inl ⟨F, hF, hFo, rfl, rfl, rfl, cv, hcv, rfl⟩⟩
      · exact hrr
      · exact hDs'
      · rw [hps']; simp [vars_length']
    · exfalso
      rw [hjo] at hlo
      have := List.getElem?_eq_none_iff.mpr hlo
      rw [this] at hFo; cases hFo
  · rcases CompilationData.ctorApp_cases hdata j hres with
      ⟨F', hF', hF'o, -⟩ | ⟨a', ha', hlo', hao', cv, hcv, hcn, hm2⟩
    · exfalso
      rw [hjo] at hF'o
      have := List.getElem?_eq_none_iff.mpr hlo
      rw [this] at hF'o; cases hF'o
    · obtain ⟨rfl, rfl, hps⟩ := mkApps_const_inj hm2
      rw [hjnf] at hps
      have hps' := List.append_cancel_right hps
      rw [hjo] at hao'
      rw [hao] at hao'; cases hao'
      refine ⟨_, _, Ds, idx, R, Es, doms₀, TbH, _, _, _, _, _, _, hl', ?_, htype, ?_, hidx2,
        hmot'', hEs', hTh, hdoms', ?_, .inr ⟨a, ha, hlo, hao, rfl, rfl, rfl, cv, hcv, rfl⟩⟩
      · exact hrr
      · exact hDs'
      · rw [hps']; simp

end Lean4Lean.ShapeModel
