import Lean4Lean.Theory.Typing.StructureMajorProvenance
import Lean4Lean.Theory.Typing.CaseReduction

/-! Structure majors of registered case eliminators.

A case schema is registered (`VEnv.WF'.inductEliminators`) over a base
environment that is only required to agree with the current one on its
equations and to contain the certified declaration's constants. Nothing ties
the certified declaration to the projection metadata already registered for
the same family names. The resulting gap is genuine: the confluence of the
full reduction fails without the coherence hypothesis below.

Counterexample. Start from the empty environment and register, by
`inductProjections` over the axioms `S : Type` and `S.a : S`, the structure
`structure S : Type where a ::` (one constructor `S.a`, no parameters, no
fields). Add the axiom `S.b : S`, and register by `inductEliminators`, over
the empty base, the case schema of `inductive S : Type | b : S`. Every premise
holds: the schema is certified over the empty base, the environment contains
the constants `S` and `S.b` at that declaration's values, no equation was
added, the schema needs no projection names, and its key is fresh. In a
context with a motive `m : S → Type` and a minor `x : m S.b`, the case
application `elim S (m, x) S.b` computes to `x`, while structure eta gives
`S.b ≡ S.a`, so the same application is definitionally equal to
`elim S (m, x) S.a`, which has no rule and no reduct other than eta
re-expansions; `x` and it are not normally equal, and proof irrelevance does
not apply at `Type`. Hence `IsDefEq.full_church_rosser` is false for this
well-formed environment, and the case-schema structure-major fact needs
`VEnv.EliminatorsCoherent`.

Decision (2026-10-07): this was a specification defect. `inductEliminators`
now requires `VInductDecl.ProjectionsCoherent` (Theory/Typing/Env.lean), which
excludes the example above, and `VEnv.WF.eliminatorsCoherent`
(EliminatorCoherenceOfWF.lean) derives `VEnv.EliminatorsCoherent` from
`VEnv.WF`. No producer in the verified pipeline registers schemas for foreign
projection metadata: `Certified.register_after_constructors` proves the premise
from freshness, and `CheckingEnv.Valid.registerCases` takes it. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
open private reduction_head_app reduction_head_mkApps restoration_vars view_constructor_external
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas

/-- The constructor major of a generated case rule is the restored generated
constructor application: its head is the restored constructor name, it ends
with exactly the rule's captured field variables, and its parameter prefix is
the common parameters or the certified container arguments. -/
theorem Generates.ctor_shape {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hgen : schema.Generates block owner rule) :
    ∃ index : Fin (schema.view owner).constructors.size,
      rule.application.ctorName =
        schema.restoration.headName (schema.view owner).constructors[index].name ∧
      ((schema.restoration.heads.find? (fun h => h.auxiliary ==
          (schema.view owner).constructors[index].name) = none ∧
        rule.application.ctorArguments.length = schema.signature.params.length + rule.numFields) ∨
      ∃ spec, schema.restoration.heads.find? (fun h => h.auxiliary ==
          (schema.view owner).constructors[index].name) = some spec ∧
        rule.application.ctorArguments.length = spec.arguments.length +
          (schema.signature.params.length - spec.nparams) + rule.numFields) := by
  obtain ⟨rules, hg, hm, he⟩ := hgen
  obtain ⟨index, hrestore⟩ := equation_origin hg hm
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  have hnoRec := view_constructor_external (schema := schema) (owner := owner) index
  obtain ⟨ds', lhs', rhs', type', hl', hr', _, hel, her, het, _⟩ :=
    restored_common_telescope hl hr ht
  have hrhs : rhs' = VExpr.mkApps (.bvar (nf + (schema.view owner).constructors.size - 1 - index.val))
      (vars nf 0) := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some rhs' at hr'
    simp only [hnoRec, List.map_nil, List.append_nil] at hr'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hr'
    rw [restoration_mkApps] at hr'
    simp [restoration_vars, Restoration.expr.go] at hr'
    exact hr'.symm
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  have hlhs0 : schema.restoration.expr
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices ++ [major])) = some lhs' := by
    simpa only [Instance.recursorHead, hzero, Nat.add_zero] using hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp [List.mapM_append, restoration_vars, List.mapM_cons, Restoration.expr.go] at hlhs0
  obtain ⟨allArgs, ⟨restArgs, ⟨indices', hi, majorArgs, ⟨major', hmajor, rfl⟩, rfl⟩, rfl⟩, hout⟩ := hlhs0
  have hlhs : lhs' = .app
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices')) major' := by
    simpa [VExpr.mkApps, List.foldl_append] using hout.symm
  have hmParams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ (schema.view owner).params.length :=
    hparams
  obtain ⟨cl, cargs, hmajEq⟩ := Restoration.const_mkApps hmajor
  have hcount := restored_ctorApp_count hmParams hmajor
  have ha : Application.extract lhs' = some
      ⟨block, owner.val, g.targetLevel :: g.levels, vars np nf ++ indices',
        schema.restoration.headName ctor.name, cl, cargs⟩ := by
    rw [hlhs, hmajEq]
    simp only [Application.extract,
      spine_mkApps_exact (.elim block owner.val (g.targetLevel :: g.levels)) _ rfl,
      spine_mkApps_exact (.const (schema.restoration.headName ctor.name) cl) _ rfl]
  have hhead : lhs'.getAppFnArgs.1 = .elim block owner.val (g.targetLevel :: g.levels) := by
    rw [hlhs, reduction_head_app]
    exact reduction_head_mkApps _ _
  have hb := extract_wrap (rhs := rhs') (type := type') hhead ds'
  rw [← hel, ← her, ← het] at hb
  simp [AppliedRule.extract, hb, ha] at he
  have hnf : rule.numFields = nf := by
    rw [← he]
    simp only [AppliedRule.numFields]
    rw [hrhs, spine_mkApps_exact _ _ rfl]
    simp [vars]
  have hargsEq : rule.application.ctorArguments = cargs := by rw [← he]
  have hcargs : major'.getAppFnArgs.2 = cargs := by rw [hmajEq, spine_mkApps_exact _ _ rfl]
  refine ⟨index, by rw [← he], ?_⟩
  rw [hargsEq, hnf, ← hcargs]
  exact hcount

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
set_option linter.unusedSectionVars false

variable {env : VEnv}

/-- Every registered case eliminator is certified by a source declaration
whose constants are present and which owns the projection metadata of its
original families. It follows from well-formedness (`VEnv.WF.eliminatorsCoherent`). Nested containers need no premise: they
are certified installations, whose projection metadata is coherent in every
well-formed environment. -/
def EliminatorsCoherent (env : VEnv) : Prop :=
  ∀ key schema, env.eliminators key schema → ∃ base source block,
    base ≤ env ∧ schema.Certified base source block ∧
    (∀ value ∈ block.types ++ block.ctors, env.constants value.name = some value.toVConstant) ∧
    ∀ type ∈ source.types, ∀ info, env.projections type.name info →
      (⟨type.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries

theorem CaseStep.generated (H : CaseStep env U Γ rule levels arguments) :
    ∃ block schema owner, env.eliminators block schema ∧ schema.Generates block owner rule := by
  cases H with
  | iota hl hg => exact ⟨_, _, _, hl, hg⟩

private theorem instL_wrapForalls'' (ds : List VExpr) (body : VExpr) (packed : List VLevel) :
    (VExpr.wrapForalls ds body).instL packed =
      VExpr.wrapForalls (ds.map (·.instL packed)) (body.instL packed) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [VExpr.wrapForalls, List.foldr_cons, List.map_cons, VExpr.instL] at ih ⊢; rw [ih]

/-- A saturated constant application at a rigid family type supplies the
constant's whole telescope, and its declared result family is that family. -/
theorem HasType.const_spine_family (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hci : env.constants c = some ci) (hres : ci.type.forallResult.getAppFnArgs.1 = .const F lsF)
    (hF : env.Rigid F) (hG : env.Rigid G)
    (hs : env.HasType U Γ (VExpr.mkApps (.const c lsc) fs) (VExpr.mkApps (.const G ls) ps)) :
    fs.length = ci.type.forallArity ∧ F = G := by
  have hhead : VExpr.WF env U Γ (.const c lsc) := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hs⟩
  obtain ⟨ci', hci', hlw, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hci] at hci'
  cases hci'
  have hc := HasType.const (Γ := Γ) hci hlw hlen
  obtain ⟨doms, hdoms, hdomsLen⟩ := VExpr.forallResult_telescope ci.type
  have hresEq : ci.type.forallResult =
      VExpr.mkApps (.const F lsF) ci.type.forallResult.getAppFnArgs.2 := by
    have h := VExpr.mkApps_getAppFnArgs_eq ci.type.forallResult
    change VExpr.mkApps ci.type.forallResult.getAppFnArgs.1 ci.type.forallResult.getAppFnArgs.2 = _ at h
    rw [hres] at h
    exact h.symm
  rw [hdoms, hresEq, instL_wrapForalls'', VExpr.instL_mkApps] at hc
  obtain ⟨hfs, hFG⟩ := HasType.mkApps_rigid_family henv hΓ hF hG hc hs
  simp only [List.length_map] at hfs
  exact ⟨hfs.trans hdomsLen, hFG⟩

/-- A case major of structure type is a saturated application of the
structure's constructor, and the case rule captures only its fields. This
needs `EliminatorsCoherent`, which is not a consequence of `env.WF`. -/
theorem MatchedCaseStep.struct_major (henv : env.WF) (hcoh : env.EliminatorsCoherent)
    (hm : MatchedCaseStep env U Γ rule actual) (hΓ : OnCtx Γ (env.IsType U))
    (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
      (VExpr.mkApps (.const family ls) ps)) :
    actual.ctorName = info.ctorName ∧
      actual.ctorArguments.length = info.nparams + info.numFields ∧
      rule.numFields ≤ info.numFields := by
  obtain ⟨block, schema, owner, hlookup, hgen⟩ := hm.source.generated
  obtain ⟨base, source, sblock, hbaseLe, hcert, hconst, hproj⟩ := hcoh block schema hlookup
  have hcert' := hcert
  obtain ⟨expanded, g, aux, hdata, hprior, hres, hfam⟩ := hcert
  have hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length :=
    fun h hh => Nat.le_of_eq (hcert'.restoration_nparams h hh)
  obtain ⟨index, hname, hcount⟩ := hgen.ctor_shape hparams
  obtain ⟨sctor, hsctor, _, hvc⟩ := view_constructor_origin index
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hsctor
  have hi' : i < schema.signature.constructors.size := by simpa using hi
  let sidx : Fin schema.signature.constructors.size := ⟨i, hi'⟩
  have hsidx : schema.signature.constructors[sidx] = sctor := by
    simpa only [sidx, Fin.getElem_fin, Array.getElem_toList] using hget
  have hvname : (schema.view owner).constructors[index].name =
      schema.signature.constructors[sidx].name := by
    rw [hvc, hsidx]; rfl
  rw [hvname, hres] at hname hcount
  have hctorEq : actual.ctorName = (compilationRestoration source aux).headName
      schema.signature.constructors[sidx].name := hm.ctor_eq.trans hname
  have hlenEq : actual.ctorArguments.length = rule.application.ctorArguments.length :=
    hm.ctorArguments_length
  have hnp := hdata.model.nparams.trans hdata.nparams
  obtain ⟨envTypes, direct, _, _, hwf, _⟩ := hdata.correspondence
  rcases hdata.constructor_origin sidx with ⟨type, htype, ctor, hctor, hn⟩ | ⟨a, ha, actor, hactor, hn⟩
  · have hsourceName : schema.signature.constructors[sidx].name ∈ familyNames source.types := by
      rw [hn]
      exact List.mem_flatMap.mpr ⟨type, htype, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
    rcases hcount with ⟨_, hlen⟩ | ⟨spec, hfind, _⟩
    · rw [hdata.headName_source hsourceName, hn] at hctorEq
      have hmem : ctor ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨type, htype, hctor⟩
      have hlookup' : env.constants ctor.name = some ctor.toVConstant :=
        hconst ctor (List.mem_append_right _ (by rw [hdata.ctors]; exact hmem))
      obtain ⟨lsF, hresF⟩ := (CompiledInductive.intro hdata hprior).ctor_result type htype ctor hctor
      have hrigid : env.Rigid type.name := nativeHeadRigid_iff.mp
        (henv.case_original_family_rigid hlookup (by rw [hfam]; exact List.mem_map.mpr ⟨type, htype, rfl⟩))
      rw [hctorEq] at hs
      obtain ⟨harity, hF⟩ := HasType.const_spine_family henv hΓ hlookup' hresF hrigid
        (henv.projectionRigid hl) hs
      subst hF
      have hentry := hproj type htype info hl
      obtain ⟨type', htype', c', hct', heq⟩ := VInductDecl.projectionEntries_origin hentry
      simp only [VProjectionEntry.mk.injEq] at heq
      obtain ⟨htn, rfl⟩ := heq
      have htt : type = type' :=
        VInductDecl.type_eq_of_mem_name hdata.sourceWF.2.1 htype htype' htn
      subst htt
      rw [hct'] at hctor
      obtain rfl := List.mem_singleton.mp hctor
      refine ⟨hctorEq, ?_, ?_⟩
      · simp only [VProjectionInfo.numFields]
        change actual.ctorArguments.length = ctor.type.forallArity at harity
        omega
      · simp only [VProjectionInfo.numFields]
        change actual.ctorArguments.length = ctor.type.forallArity at harity
        omega
    · have hm' := List.mem_of_find?_eq_some hfind
      have hsn : spec.auxiliary = schema.signature.constructors[sidx].name := by
        simpa using List.find?_some hfind
      exact (hdata.source_head_disjoint hsourceName (List.mem_map.mpr ⟨spec, hm', hsn⟩)).elim
  · have hmem : (⟨a.constructorName actor, source.uvars, source.nparams, actor.name, a.levels,
        a.arguments⟩ : HeadSpecialization) ∈ (compilationRestoration source aux).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨actor, hactor, rfl⟩)⟩
    have hf := Restoration.find_of_mem hdata.restorationScoped hmem
    rcases hcount with ⟨hfind, _⟩ | ⟨spec, hfind, hlen⟩
    · rw [← hn, hfind] at hf; cases hf
    rw [← hn, hfind] at hf
    cases hf
    rw [hn, hdata.headName_auxiliary_constructor ha hactor] at hctorEq
    obtain ⟨b0, cblock, inst0, hc0, hi0, hle0⟩ :=
      VEnv.CertifiedSpecializations.container_installed hprior ha
    have hle : inst0 ≤ env := hle0.trans hbaseLe
    have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
    have hcmem : actor ∈ a.container.constructorConstants :=
      List.mem_flatMap.mpr ⟨a.source, hsrc, hactor⟩
    obtain ⟨eq, heq, fn, lv, args, hmaj⟩ := hc0.constructor_equation actor hcmem
    have hdf : env.defeqs eq := hle.defeqs (VInductBlock.install_rule hi0 heq)
    rw [hctorEq] at hs
    obtain ⟨hcn, hlenStruct⟩ := henv.installed_major_struct hΓ hdf ⟨fn, lv, args, hmaj⟩ hl hs
    obtain ⟨lsF, hresF⟩ := hc0.ctor_result a.source hsrc actor hactor
    have hlookup' : env.constants actor.name = some actor.toVConstant :=
      hle.constants (VInductBlock.install_ctor_lookup hi0 (by rw [hc0.ctors_eq]; exact hcmem))
    have hF := (henv.ordered.projection_resultFamily hl).unique
      (hcn ▸ (⟨_, lsF, hlookup', hresF⟩ : env.ResultFamily actor.name a.source.name))
    subst hF
    obtain ⟨_, _, hnparams⟩ := CompiledInductive.family_projection henv hc0 hi0 hle hsrc hactor hl
    have hwfa := (hwf a ha).1
    refine ⟨hctorEq.trans hcn, hlenStruct, ?_⟩
    simp only at hlen
    omega

end Lean4Lean.VEnv
