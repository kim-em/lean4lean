import Lean4Lean.Theory.Typing.CaseMotive
import Lean4Lean.Theory.Typing.CaseMajorDomain
import Lean4Lean.Theory.Inductive.RestorationHead

/-! The source sort of a restored case family is justified by its native
family header and the finite compilation correspondence. -/

namespace Lean4Lean.InductiveSignature

/-- The original native header is definitionally equal to a telescope ending
in the family sort recorded by the normalized source signature. -/
theorem CompilationData.original_family_header {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hfamily : family ∈ source.types) :
    ∃ envTypes, base.addConstVals source.typeConstants = some envTypes ∧
      ∃ domains level, level ≈ family.resultLevel ∧
        envTypes.IsDefEqU source.uvars [] family.type (VExpr.wrapForalls domains (.sort level)) := by
  obtain ⟨envTypes, direct, htypes, _, _, hfamilies⟩ := H.correspondence
  obtain ⟨normalized, hnormalized, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    hfamilies family (List.mem_append_left _ hfamily)
  obtain ⟨⟨sigFamily, index⟩, _, rfl⟩ := List.mem_map.mp hnormalized
  obtain ⟨restored, hrestore, htype⟩ := hrel.type
  obtain ⟨domains, hdomains⟩ := Restoration.forall_sort_shape hrestore
  refine ⟨envTypes, htypes, domains, sigFamily.resultLevel, hrel.resultLevel, ?_⟩
  rw [hdomains] at htype
  exact htype.symm

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv

private theorem addConst_le_target {base added current : VEnv}
    (hle : base ≤ current) (hadd : base.addConst name ci = some added)
    (hvalue : current.constants name = some ci) : added ≤ current := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    refine ⟨?_, hle.defeqs, hle.projections, hle.eliminators⟩
    intro n value hv
    change (if name = n then some ci else base.constants n) = some value at hv
    split at hv
    · rename_i hn
      cases hn
      cases Option.some.inj hv
      exact hvalue
    · exact hle.constants hv

/-- A successful header extension embeds into any later environment that
contains the same exact headers and extends its original base. -/
theorem addConstVals_le_target {base added current : VEnv}
    (hle : base ≤ current) (hadd : base.addConstVals values = some added)
    (hvalues : ∀ value ∈ values, current.constants value.name = some value.toVConstant) :
    added ≤ current := by
  induction values generalizing base with
  | nil =>
    have he : base = added := Option.some.inj hadd
    cases he
    exact hle
  | cons value values ih =>
    cases hv : base.addConst value.name value.toVConstant with
    | none => simp [VEnv.addConstVals, hv] at hadd
    | some next =>
      have ht : next.addConstVals values = some added := by
        simpa only [VEnv.addConstVals, hv, bind, Option.bind_some] using hadd
      exact ih (addConst_le_target hle hv (hvalues value (.head _))) ht
        fun value hmem => hvalues value (.tail _ hmem)

end Lean4Lean.VEnv

namespace Lean4Lean

/-- Every finite source header retains a normalized telescope ending in its
recorded family sort in an environment where its exact constants are present. -/
theorem CompiledInductive.original_family_header (H : CompiledInductive base source block) :
    ∀ (current : VEnv), base ≤ current →
      (∀ family ∈ source.types,
        current.constants family.name = some family.toVConstant) →
      ∀ family ∈ source.types, ∃ domains level,
        family.uvars = source.uvars ∧ level ≈ family.resultLevel ∧
          current.IsDefEqU source.uvars [] family.type (VExpr.wrapForalls domains (.sort level)) := by
  exact CompiledInductive.rec
    (motive_1 := fun base source _ _ =>
      ∀ current : VEnv, base ≤ current →
        (∀ family ∈ source.types, current.constants family.name = some family.toVConstant) →
        ∀ family ∈ source.types, ∃ domains level,
          family.uvars = source.uvars ∧ level ≈ family.resultLevel ∧
            current.IsDefEqU source.uvars [] family.type (VExpr.wrapForalls domains (.sort level)))
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ current hle hconstants family hfamily => by
      obtain ⟨envTypes, htypes, domains, level, hlevel, htype⟩ :=
        hdata.original_family_header hfamily
      have htypesLE := VEnv.addConstVals_le_target hle htypes (by
        intro value hvalue
        obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
        exact hconstants family hfamily)
      exact ⟨domains, level, hdata.sourceWF.2.2.1 family hfamily, hlevel, htype.mono htypesLE⟩)
    (fun _ hle _ ih current hcurrent hconstants family hfamily =>
      ih current (hle.trans hcurrent) hconstants family hfamily)
    trivial (fun _ _ _ _ _ _ _ => trivial) H

/-- Finite replay preserves the exact original family constant list. -/
theorem CompiledInductive.source_type_constants (H : CompiledInductive base source block) :
    block.types = source.typeConstants := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source block _ => block.types = source.typeConstants)
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ => hdata.types) (fun _ _ _ ih => ih)
    trivial (fun _ _ _ _ _ _ _ => trivial) H

private theorem install_base_le (H : VInductBlock.install base block = some installed) :
    base ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
    VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

private theorem install_type_lookup (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.types) : installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact ((VEnv.addConstVals_le hc).trans <| VEnv.addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le).constants (VEnv.addConstVals_get ht hvalue)

/-- Every certified container retains both its exact native family lookup
and its normalized result-sort telescope in the specialization environment. -/
theorem CertifiedSpecializations.family_header (H : CertifiedSpecializations env auxiliaries) :
    ∀ a ∈ auxiliaries, ∀ family ∈ a.container.types,
      env.constants family.name = some family.toVConstant ∧
      ∃ domains level, family.uvars = a.container.uvars ∧ level ≈ family.resultLevel ∧
        env.IsDefEqU a.container.uvars [] family.type (VExpr.wrapForalls domains (.sort level)) := by
  exact CertifiedSpecializations.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun env auxiliaries _ =>
      ∀ a ∈ auxiliaries, ∀ family ∈ a.container.types,
        env.constants family.name = some family.toVConstant ∧
        ∃ domains level, family.uvars = a.container.uvars ∧ level ≈ family.resultLevel ∧
          env.IsDefEqU a.container.uvars [] family.type (VExpr.wrapForalls domains (.sort level)))
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (by simp)
    (fun {env a rest base block installed} hcompile _ hinstall hle _ _ ih => by
      intro a ha family hfamily
      rcases List.mem_cons.mp ha with rfl | ha
      · have hconstants : ∀ family ∈ a.container.types,
            env.constants family.name = some family.toVConstant := by
          intro family hfamily
          apply hle.constants
          apply install_type_lookup hinstall
          rw [hcompile.source_type_constants]
          exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
        exact ⟨hconstants family hfamily,
          hcompile.original_family_header env ((install_base_le hinstall).trans hle)
            hconstants family hfamily⟩
      · exact ih a ha family hfamily)
    H

end Lean4Lean

namespace Lean4Lean.VEnv
open Lean4Lean
variable {env : VEnv} {U : Nat}
open VExpr

private theorem constant_normalized_header (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hlookup : env.constants name = some ci)
    (hheader : env.IsDefEqU N [] ci.type (VExpr.wrapForalls domains (.sort level)))
    (hlevels : ∀ l ∈ levels, l.WF U) (hlen : levels.length = ci.uvars) :
    env.HasType U Γ (.const name levels)
      (VExpr.wrapForalls (domains.map (instL levels)) (.sort (level.inst levels))) := by
  have hconst := HasType.const hlookup hlevels hlen (Γ := Γ)
  have he := (hheader.instL hlevels).weak0 henv.ordered (Γ := Γ)
  simpa only [instL_wrapForalls, instL] using hconst.defeqU_r henv hΓ he

end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature

private theorem ContainerSpecialization.directFamily_resultLevel
    {a : ContainerSpecialization} {U : Nat} {params : List VExpr} {direct : VInductiveType}
    (H : a.directFamily U params = some direct) :
    direct.resultLevel = a.source.resultLevel.inst a.levels := by
  unfold ContainerSpecialization.directFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, ctors, _, he⟩ := H
  cases Option.some.inj he
  rfl

namespace CaseSchema

/-- A restored case family's native head has a telescope ending in the
specialized source sort. Both original families and certified containers are
justified by their actual native header constants. -/
theorem Certified.family_head_type {schema : CaseSchema}
    (H : schema.Certified base source sourceBlock)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hle : base ≤ env)
    (hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant)
    (owner : Fin schema.signature.families.size)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlen : levels.length = schema.signature.uvars) :
    ∃ domains level,
      env.HasType U Γ
        (.const (schema.restoration.headName schema.signature.families[owner].name)
          (schema.restoration.headLevels schema.signature.families[owner].name levels))
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ schema.sourceLevel owner levels := by
  obtain ⟨expanded, g, auxiliaries, hdata, hprior, hr, _⟩ := H
  obtain ⟨envTypes, direct, htypes, hdirect, hargs, hfamilies⟩ := hdata.correspondence
  have htypesLE := VEnv.addConstVals_le_target hle htypes (by
    intro value hvalue
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
    exact hconstants family hfamily)
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (schema.signature.declarationFamily_mem owner)
  have hname : schema.signature.families[owner].name = family.name := hrel.name
  have hsourceUvars : schema.signature.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  rcases List.mem_append.mp hfamily with hfamily | hfamily
  · have hfamilyName : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hfamily, List.mem_cons_self⟩
    obtain ⟨restored, hrestore, hheader⟩ := hrel.type
    obtain ⟨domains, hdomains⟩ := Restoration.forall_sort_shape hrestore
    rw [hdomains] at hheader
    have htyped := VEnv.constant_normalized_header henv hΓ (hconstants family hfamily)
      (hheader.symm.mono htypesLE) hlevels
      (hlen.trans (hsourceUvars.trans (hdata.sourceWF.2.2.1 family hfamily).symm))
    rw [hr, hname, hdata.headName_source hfamilyName, hdata.headLevels_source hfamilyName]
    exact ⟨_, _, htyped, rfl⟩
  · obtain ⟨a, ha, hfamily⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hfamily
    have hfamilyName := ContainerSpecialization.directFamily_name hfamily
    have hfamilyLevel := ContainerSpecialization.directFamily_resultLevel hfamily
    let spec : HeadSpecialization := {
      auxiliary := a.auxiliary, uvars := source.uvars, nparams := source.nparams,
      target := a.source.name, levels := a.levels, arguments := a.arguments }
    have hspec : spec ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hhead := Restoration.headName_of_mem hdata.restorationScoped hspec
    have hheadLevels := Restoration.headLevels_of_mem (levels := levels) hdata.restorationScoped hspec
    obtain ⟨hlookup, domains, level, hfamilyUvars, hlevel, hheader⟩ :=
      hprior.family_header a ha a.source (List.getElem_mem a.family.isLt)
    have hnativeWF : ∀ l ∈ a.levels.map (·.inst levels), l.WF U := by
      intro l hl
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hl
      exact VLevel.WF.inst hlevels
    have hnativeLength : (a.levels.map (·.inst levels)).length = a.source.uvars := by
      simpa only [List.length_map, hfamilyUvars] using (hargs a ha).2.2.1
    have htyped := VEnv.constant_normalized_header henv hΓ (hle.constants hlookup)
      (hheader.mono hle) hnativeWF hnativeLength
    rw [hr, hname, hfamilyName, hhead, hheadLevels]
    refine ⟨_, _, htyped, ?_⟩
    change level.inst (a.levels.map (·.inst levels)) ≈
      schema.signature.families[owner].resultLevel.inst levels
    have hsourceLevel : schema.signature.families[owner].resultLevel ≈
        a.source.resultLevel.inst a.levels := by
      simpa only [hfamilyLevel, declarationFamily] using hrel.resultLevel
    exact (VLevel.inst_congr_l hlevel).trans (by
      rw [← VLevel.inst_inst]
      exact (VLevel.inst_congr_l hsourceLevel).symm)

end CaseSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.InductiveSignature.CaseSchema

theorem genericLevels_inst {schema : CaseSchema}
    (hlen : levels.length = schema.signature.uvars) :
    schema.genericLevels.map (VLevel.inst (target :: levels)) = levels := by
  have h := VLevel.inst_map_id (ls := target :: levels)
    (n := schema.genericUvars) (by simp [genericUvars, hlen])
  have h' : target :: schema.genericLevels.map (VLevel.inst (target :: levels)) =
      target :: levels := by
    simpa [VLevel.params, genericUvars, genericLevels, List.range_succ_eq_map,
      List.map_map, Function.comp_def, VLevel.inst] using h
  exact List.cons.inj h' |>.2

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open Lean4Lean VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

/-- The major argument's family type has the source universe recorded by
the installed schema, including universe specialization through restoration. -/
theorem HasType.caseMajor_source_sort (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {target : VLevel} {args : List VExpr} {major : VExpr}
    (hlookup : env.eliminators block schema)
    (hpermission : schema.Permission U owner levels target)
    (hlen : args.length = caseMajorArity schema owner)
    (H : VExpr.WF env U Γ
      (VExpr.mkApps (.elim block owner.val (target :: levels)) (args ++ [major]))) :
    ∃ type level, env.HasType U Γ major type ∧ env.HasType U Γ type (.sort level) ∧
      level ≈ schema.sourceLevel owner levels := by
  obtain ⟨base, source, native, _, hle, hcert, _, hconstants⟩ :=
    henv.eliminator_origin hlookup
  have hsource : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := by
    intro family hfamily
    obtain ⟨expanded, g, auxiliaries, hdata, _⟩ := hcert
    apply hconstants family.toVConstVal
    apply List.mem_append_left
    rw [hdata.types]
    exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
  obtain ⟨domains, level, hhead, hlevel⟩ := hcert.family_head_type henv
    (Γ := []) (U := schema.genericUvars) True.intro hle hsource owner
    (levels := schema.genericLevels)
    (by simp [genericLevels, genericUvars, VLevel.WF])
    (by simp [genericLevels])
  have hhead' := (hhead.instL hpermission.packedWF).weak0 henv.ordered (Γ := Γ)
  simp only [instL_wrapForalls, VExpr.instL] at hhead'
  obtain ⟨familyArgs, hmajor⟩ := HasType.caseMajor_type henv hΓ hlookup hlen H
  obtain ⟨_, hfamily⟩ := hmajor.isType henv.ordered hΓ
  have hargsLength := HasType.mkApps_sort_arity henv hΓ hhead' hfamily
  have hfamilySort := (HasType.mkApps_wrapForalls henv hΓ hhead' ⟨_, hfamily⟩
    hargsLength).2
  simp only [instOuter_sort] at hfamilySort
  refine ⟨_, _, hmajor, hfamilySort, ?_⟩
  have heq := VLevel.inst_congr_l (ls := target :: levels) hlevel
  simpa only [sourceLevel, VLevel.inst_inst, genericLevels_inst hpermission.length] using heq

/-- A case application whose source is always nonzero cannot inspect a
proof. This is derived from typing, rather than added to the schema contract. -/
theorem HasType.caseMajor_not_proof (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {target : VLevel} {args : List VExpr} {major proposition : VExpr}
    (hlookup : env.eliminators block schema)
    (hpermission : schema.Permission U owner levels target)
    (hlen : args.length = caseMajorArity schema owner)
    (H : VExpr.WF env U Γ
      (VExpr.mkApps (.elim block owner.val (target :: levels)) (args ++ [major])))
    (hnever : (schema.sourceLevel owner levels).IsNeverZero)
    (hprop : env.HasType U Γ proposition (.sort .zero))
    (hproof : env.HasType U Γ major proposition) : False := by
  obtain ⟨type, level, hmajor, htype, hlevel⟩ :=
    HasType.caseMajor_source_sort henv hΓ hlookup hpermission hlen H
  have hsame := hmajor.uniqU henv hΓ hproof
  have hprop' := htype.defeqU_l henv hΓ hsame
  have hzero := (hprop'.uniqU henv hΓ hprop).sort_inv henv hΓ
  exact hnever [] (VLevel.equiv_def.mp (hlevel.symm.trans hzero) [])

/-- When a matched constructor is a proof, the case permission forces the
result into Prop. This supplies the proof-irrelevance branch of compatibility. -/
theorem MatchedCaseStep.result_prop_of_major_proof (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : MatchedCaseStep env U Γ rule actual)
    {proposition : VExpr}
    (hprop : env.HasType U Γ proposition (.sort .zero))
    (hproof : env.HasType U Γ
      (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
      proposition) :
    ∃ resultType, env.HasType U Γ resultType (.sort .zero) ∧
      env.HasType U Γ actual.expr resultType := by
  apply H.result_prop_of_target_zero henv hΓ
  have hsource := H.source
  generalize hpacked : actual.levels = packed at hsource
  cases hsource with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    have htarget : target ≈ .zero := by
      rcases hp.admissible with hnever | hzero
      · obtain ⟨base, source, sourceBlock, hbase, _, hcert, _, _⟩ :=
          henv.eliminator_origin hl
        have harity := hcert.arguments_length hbase hg
        obtain ⟨hb, ho⟩ := hg.owned
        have hab : actual.block = block := H.block_eq.trans hb
        have hao : actual.owner = owner.val := H.owner_eq.trans ho
        have ht : VExpr.WF env U Γ (VExpr.mkApps
            (.elim block owner.val (target :: levels))
            (actual.arguments ++ [VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
              actual.ctorArguments])) := by
          obtain ⟨type, hguard⟩ := H.guard
          refine ⟨type, ?_⟩
          simpa only [HasType, Application.expr, VExpr.mkApps, List.foldl_append,
            List.foldl_cons, List.foldl_nil,
            hab, hao, hpacked] using hguard.hasType.1
        exact False.elim (HasType.caseMajor_not_proof henv hΓ hl hp
          (H.arguments_length.trans harity) ht hnever hprop hproof)
      · exact hzero
    simpa only [hpacked, List.head?_cons, Option.getD_some] using htarget

end Lean4Lean.VEnv
