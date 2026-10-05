import Lean4Lean.Verify.Typing.ProjectionDesugaring
import Lean4Lean.Theory.Typing.RigidHeadStrengthening

/-! Semantic inverse transport for generated projection occurrences. -/

namespace Lean4Lean
open VExpr InductiveSignature InductiveSignature.CaseSchema

private theorem registered_original_header {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (hlookup : env.eliminators key schema)
    (horiginal : name ∈ schema.originalFamilies)
    (hfamily : schema.signature.families[owner].name = name)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlen : levels.length = schema.signature.uvars) :
    ∃ domains level, env.HasType U Γ (.const name levels) (wrapForalls domains (.sort level)) := by
  obtain ⟨base, source, native, _, hle, hcert, _, hconstants⟩ := henv.eliminator_origin hlookup
  have hsource : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := by
    intro family hfamily
    obtain ⟨expanded, g, auxiliaries, hdata, _⟩ := hcert
    apply hconstants family.toVConstVal
    apply List.mem_append_left
    rw [hdata.types]
    exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
  obtain ⟨domains, level, hhead, _⟩ := hcert.family_head_type henv hΓ hle hsource owner hlevels hlen
  obtain ⟨expanded, g, auxiliaries, hdata, _, hr, hnames⟩ := hcert
  rw [hnames] at horiginal
  obtain ⟨family, hmem, hname⟩ := List.mem_map.mp horiginal
  have hsourceName : name ∈ familyNames source.types := by
    rw [← hname]
    exact List.mem_flatMap.mpr ⟨family, hmem, List.mem_cons_self⟩
  rw [hr, hfamily, hdata.headName_source hsourceName, hdata.headLevels_source hsourceName] at hhead
  exact ⟨domains, level, hhead⟩

private theorem mkApps_defeq {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hargs : List.Forall₂ (env.IsDefEqU U Γ) args args')
    (hfn : env.IsDefEqU U Γ fn fn')
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    env.IsDefEqU U Γ (mkApps fn args) (mkApps fn' args') := by
  induction hargs generalizing fn fn' with
  | nil => exact hfn
  | cons ha has ih =>
    have happ : VExpr.WF env U Γ (.app fn _) := H.of_mkApps henv.ordered hΓ
    obtain ⟨A, B, hf, hx⟩ := happ.app_inv henv.ordered hΓ
    exact ih ⟨_, (hfn.of_l henv hΓ hf).appDF (ha.of_l henv hΓ hx)⟩ H

private theorem forall₂_symm {α : Type} {R : α → α → Prop} {xs ys : List α}
    (hsym : ∀ a b, R a b → R b a) (H : List.Forall₂ R xs ys) : List.Forall₂ R ys xs := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hsym _ _ h) ih

namespace ProjectionDesugaring
open VEnv VEnv.Params
variable [VEnv.Params]

/-- The implicit arguments of a projection can be reconstructed after
removing binders unused by its major term. They are recovered semantically,
so the original hidden arguments need not themselves be syntactic lifts. -/
theorem exists_weak'_inv
    (H : ProjectionDesugaring env univs Γ' name index (major.lift' ρ) target)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') :
    ∃ target', ProjectionDesugaring env univs Γ name index major target' := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hΓ := hΓ'.weak'_inv henv W
    have hmem := List.mem_of_getElem? ho
    have hrigid := henv.case_original_family_rigid hr hmem
    obtain ⟨domains, level, hhead⟩ := registered_original_header henv hΓ' hr hmem hf
      (fun l hl => hw l (List.mem_append_right _ hl)) hlu
    obtain ⟨_, hfamily⟩ := hm.isType henv.ordered hΓ'
    have hlen := HasType.mkApps_sort_arity henv hΓ' hhead hfamily
    obtain ⟨newLevels, newArgs, hsource, hlevels, hargsLength, htypes⟩ :=
      HasType.familyApp_weak'_inv hΓ' W hrigid hhead hlen hm
    obtain ⟨_, hfamily'⟩ := hsource.isType henv.ordered hΓ
    obtain ⟨_, hhead'⟩ := (show VExpr.WF env univs Γ
      (mkApps (.const name newLevels) newArgs) from ⟨_, hfamily'⟩).of_mkApps henv.ordered hΓ
    obtain ⟨_, _, hnewLevelsWF, _⟩ := HasType.const_inv henv.ordered hΓ hhead'
    have hnewPackedWF : ∀ l ∈ fieldSorts ++ newLevels, l.WF univs := by
      intro l hl
      obtain hl | hl := List.mem_append.mp hl
      · exact hw l (List.mem_append_left _ hl)
      · exact hnewLevelsWF l hl
    have hlevelsBack : List.Forall₂ (· ≈ ·) levels newLevels :=
      forall₂_symm (fun _ _ h => h.symm) hlevels
    have hpacked : List.Forall₂ (· ≈ ·) (fieldSorts ++ levels) (fieldSorts ++ newLevels) :=
      VEnv.case_forall₂_append (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl) hlevelsBack
    have hpermission : ∀ l ∈ fieldSorts, schema.ProjectionAdmissible owner newLevels l := by
      intro l hl
      have hpermission : schema.Permission univs owner levels l :=
        ⟨hlu, fun l hl => hw l (List.mem_append_right _ hl),
          hw l (List.mem_append_left _ hl), hp l hl⟩
      exact (hpermission.congr (fun l' hl' => by
        cases hl' with
        | head => exact hw l (List.mem_append_left _ hl)
        | tail _ hh => exact hnewLevelsWF l' hh) (.cons rfl hlevelsBack)).admissible
    obtain ⟨_, hnewFamilyLarge⟩ := (hsource.weak' henv.ordered W).isType henv.ordered hΓ'
    have hlift (f : VExpr) (xs : List VExpr) :
        (mkApps f xs).lift' ρ = mkApps (f.lift' ρ) (xs.map (·.lift' ρ)) := by
      induction xs generalizing f with
      | nil => rfl
      | cons a xs ih => exact ih (.app f a)
    simp only [hlift, VExpr.lift'] at hnewFamilyLarge
    obtain ⟨_, hargs⟩ := IsDefEqU.rigidApp_inv henv hΓ' (VEnv.nativeHeadRigid_iff.mp hrigid)
      htypes hnewFamilyLarge
    have hargsBack : List.Forall₂ (env.IsDefEqU univs Γ') (params ++ indices)
        (newArgs.map (·.lift' ρ)) := forall₂_symm (fun _ _ h => h.symm) hargs
    have hfn := (VExpr.LEquiv.instL_expr program.value hw hnewPackedWF hpacked).defeq
      henv hΓ' (ht.of_mkApps henv.ordered hΓ')
    have htarget := mkApps_defeq henv hΓ'
      (VEnv.case_forall₂_append hargsBack (.cons (show env.IsDefEqU univs Γ'
        (major.lift' ρ) (major.lift' ρ) from ⟨_, hm⟩) .nil)) hfn ht
    let newParams := newArgs.take schema.signature.params.length
    let newIndices := newArgs.drop schema.signature.params.length
    have hjoin : newParams ++ newIndices = newArgs := List.take_append_drop _ _
    have hnewLength : newLevels.length = schema.signature.uvars :=
      (Lean4Lean.List.Forall₂.length_eq hlevels).trans hlu
    have hnewParams : newParams.length = schema.signature.params.length := by
      simp only [newParams, List.length_take]
      rw [List.length_append, hn, hi] at hargsLength
      omega
    have hnewIndices : newIndices.length = schema.signature.families[owner].indices.length := by
      simp only [newIndices, List.length_drop]
      rw [List.length_append, hn, hi] at hargsLength
      omega
    refine ⟨mkApps (program.value.instL (fieldSorts ++ newLevels))
      (newParams ++ newIndices ++ [major]),
      .intro hr ho hf hg hs hnewLength hfu hnewPackedWF hpermission hnewParams hnewIndices
        (by simpa only [hjoin] using hsource) ?_⟩
    apply (VExpr.WF.weak'_iff henv hΓ' W).1
    have hclosed := (program_closed hg hs).instL (ls := fieldSorts ++ newLevels)
    obtain ⟨resultType, htarget⟩ := htarget
    simpa only [hlift, hjoin, hclosed.lift'_eq Lift.Fixes.zero, List.map_append,
      List.map_cons, List.map_nil] using
      (show VExpr.WF env univs Γ' _ from ⟨_, htarget.hasType.2⟩)

end ProjectionDesugaring

end Lean4Lean
