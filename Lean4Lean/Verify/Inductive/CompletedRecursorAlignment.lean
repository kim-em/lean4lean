import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Verify.Inductive.CompletedRecursorSetup
import Lean4Lean.Verify.Inductive.Recursor.Realization
import Lean4Lean.Verify.Inductive.Recursor.GeneratedShapes

/-! Operational alignment from a joint ordinary compilation witness.

Source formation supplies raw constructor shapes. The normalized signature
supplies exact family and constructor correspondences, while generated equation
typing fixes constructor field counts. All typing arguments take place in the
already well-formed environment before equation installation; the resulting
shapes and K equalities then extend to the final environment.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace InductiveSignature

/-- The typed generated major pattern supplies exactly the fields of the raw
source constructor, by constructor saturation. -/
theorem Instance.fieldCount_of_equation {s : InductiveSignature} (g : Instance s)
    {env : VEnv} (henv : env.WF) (index : Fin s.constructors.size)
    {fields : Nat}
    (hlookup : env.constants (g.recursorName s.constructors[index].owner) =
      some (g.recursor s.constructors[index].owner).toVConstant)
    (hctor : VConstructorShape env s.constructors[index].name s.uvars s.params.length fields
      s.families[s.constructors[index].owner].indices.length
      s.families[s.constructors[index].owner].name)
    (hrigid : env.Rigid s.families[s.constructors[index].owner].name)
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hwf : (g.equation index).WF env) : fields = s.constructors[index].fields.length := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let pre := vars (s.params.length + extra) nf ++ indices
  let target := VExpr.mkApps (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (indices ++ [major])
  have hleft : env.HasType g.uvars []
      (VExpr.wrapLams domains (VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
        (pre ++ [major]))) (VExpr.wrapForalls domains target) := hwf.1
  rcases VEnv.HasType.wrapLams_inv henv (by trivial) hleft with ⟨hctx, hbody⟩
  rcases g.recursor_shape ctor.owner hlookup with ⟨hrec⟩
  have hpre : pre.length = s.params.length + s.families.size + s.constructors.size +
      s.families[ctor.owner].indices.length := by
    simp only [pre, indices, vars, List.length_append, List.length_map,
      List.length_reverse, List.length_range]
    change s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length = s.params.length + s.families.size + s.constructors.size +
        s.families[s.constructors[index].owner].indices.length
    omega
  have ⟨_, hmajor, _⟩ := hrec.spine_typing henv hctx VLevel.params_wf VLevel.params_length
    hpre ⟨_, hbody⟩
  have hsaturated := hctor.saturated_of_hasType henv hctx hrigid hmajor
  simp only [List.length_append, vars, List.length_map,
    List.length_reverse, List.length_range] at hsaturated
  change s.params.length + s.constructors[index].fields.length = s.params.length + fields at hsaturated
  omega

end InductiveSignature
theorem VInductDecl.RawCtorShape.constructorShape
    {decl : VInductDecl} {family : VInductiveType} {ctor : VConstVal} {env : VEnv}
    (H : decl.RawCtorShape family ctor) (hnames : decl.sourceNames.Nodup)
    (hfamily : family ∈ decl.types)
    (hlookup : env.constants ctor.name = some ⟨decl.uvars, ctor.type⟩) :
    ∃ fields, Nonempty (VConstructorShape env ctor.name decl.uvars decl.nparams
      fields family.numIndices family.name) := by
  rcases H with ⟨doms, result, htype, hparamsLe, hvalid, hhead⟩
  rcases hvalid with ⟨target, htarget, htargetName, levels, hfn, hlevels, hargs, hparams⟩
  rcases htargetName with hnone | htargetName
  · cases hnone
  have heq : target = family := VInductDecl.type_eq_of_mem_name hnames htarget hfamily
    (Option.some.inj htargetName).symm
  subst target
  change result.getAppFnArgs.2.length = decl.nparams + family.numIndices at hargs
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (doms.length - decl.nparams) at hparams
  refine ⟨doms.length - decl.nparams, ⟨{
    type := ctor.type
    const := hlookup
    doms := doms
    indices := result.getAppFnArgs.2.drop decl.nparams
    type_eq := ?_
    doms_length := by omega
    indices_length := by simp only [List.length_drop, hargs]; omega }⟩⟩
  rw [htype]
  congr 1
  calc
    result = VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 :=
      (VExpr.mkApps_getAppFnArgs_eq result).symm
    _ = VExpr.mkApps (.const family.name (VLevel.params decl.uvars))
        ((result.getAppFnArgs.2.take decl.nparams) ++ result.getAppFnArgs.2.drop decl.nparams) := by
      rw [List.take_append_drop, hhead]
    _ = _ := by
      rw [hparams]
      congr 2
      exact InductiveSignature.vars_eq_bvarRange _ _

namespace VerifyInductive

theorem CompletedRecursorPhasesResult.headerLE
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) : R.headerVEnv ≤ H.outVEnv :=
  R.installation.constructorLE.trans (R.ctorLE.trans H.installed.le)

theorem CompletedRecursorPhasesResult.sourceLE
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) : sourceEnv ≤ H.outVEnv :=
  R.installation.headerLE.trans H.headerLE

theorem CompletedRecursorPhasesResult.familyConstant
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.constants family.name = some family.toVConstant :=
  H.headerLE.constants (VEnv.addConstVals_get R.core.typesAdded
    (List.mem_map.mpr ⟨family, hf, rfl⟩))

theorem CompletedRecursorPhasesResult.constructorConstant
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (ctor : VConstVal) (hc : ctor ∈ decl.constructorConstants) :
    H.outVEnv.constants ctor.name = some ctor.toVConstant :=
  (R.ctorLE.trans H.installed.le).constants
    (VEnv.addConstVals_get R.core.ctorsAdded hc)

theorem CompletedRecursorPhasesResult.familyRigid
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.Rigid family.name := by
  have hsourceWF : sourceEnv.WF := R.sourceContextVEnv ▸ R.sourceContext.checking.tr.wf
  have hfresh := (VEnv.addConstVals_names_fresh R.core.typesAdded).2
    family.toVConstVal (List.mem_map.mpr ⟨family, hf, rfl⟩)
  have hrigid := hsourceWF.ordered.rigid_of_absent hfresh
  intro df hdf ls hhead
  have hdf' := H.staged.combinedAtomic.defeqs df hdf
  rw [VEnv.addProjections_defeqs] at hdf'
  exact hrigid df hdf' ls hhead

/-- Typing the normalized constructor result against its family's sort
telescope determines the number of indices. -/
theorem CompletedRecursorPhasesResult.normalizedIndexArity
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length := by
  have henv := H.outVEnvWF
  rcases hm.family s.constructors[index].owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hftype, hfctors⟩
  rcases hm.constructor index R.core.typesAdded with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  have hlookupC := H.constructorConstant ctor hctor
  have hctypeWF : H.outVEnv.IsType s.uvars [] ctor.type := by
    simpa only [VConstant.WF, ← hcuvars] using henv.ordered.constWF hlookupC
  have hnormalWF : H.outVEnv.IsType s.uvars [] (s.constructorType s.constructors[index]) :=
    hctypeWF.defeqU_l henv (by trivial)
      (by simpa only [← hm.uvars] using hctype.symm.mono H.headerLE)
  rcases VEnv.IsType.wrapForalls_inv henv (by trivial) hnormalWF with ⟨hctx, level, hresult⟩
  have hlookupF := H.familyConstant family hfamily
  have hfamilyFn := VEnv.HasType.const0 hlookupF (henv.ordered.constWF hlookupF)
  change H.outVEnv.HasType family.uvars []
    (.const family.name (VLevel.params family.uvars)) family.type at hfamilyFn
  have hfamilyFn' : H.outVEnv.HasType s.uvars []
      (.const s.families[s.constructors[index].owner].name (VLevel.params s.uvars))
      family.type := by
    simpa only [← hfuvars, hfname] using hfamilyFn
  have hnormalFn : H.outVEnv.HasType s.uvars []
      (.const s.families[s.constructors[index].owner].name (VLevel.params s.uvars))
      (VExpr.wrapForalls (s.params ++ s.families[s.constructors[index].owner].indices)
        (.sort s.families[s.constructors[index].owner].resultLevel)) :=
    hfamilyFn'.defeqU_r henv (by trivial)
      (by simpa only [← hm.uvars] using hftype.symm.mono H.sourceLE)
  have hlength := VEnv.HasType.mkApps_sort_arity henv hctx
    (hnormalFn.weak0 henv.ordered) hresult
  simpa [InductiveSignature.familyApp, InductiveSignature.vars] using hlength

theorem CompletedRecursorPhasesResult.rawConstructorShape
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    ∃ fields, Nonempty (VConstructorShape H.outVEnv s.constructors[index].name
      s.uvars s.params.length fields s.families[s.constructors[index].owner].indices.length
      s.families[s.constructors[index].owner].name) := by
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.family s.constructors[index].owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hftype, hfctors⟩
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily hfctors with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  have hcMem : ctor ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩
  have hlookup : H.outVEnv.constants ctor.name = some ⟨decl.uvars, ctor.type⟩ := by
    have := H.constructorConstant ctor hcMem
    change H.outVEnv.constants ctor.name = some ⟨ctor.uvars, ctor.type⟩ at this
    simpa only [← hcuvars, hm.uvars] using this
  have hraw := R.formation.formationWF.sourceParameterWF.rawCtorShape family hfamily ctor hctor
  rcases hraw.constructorShape hnames hfamily hlookup with ⟨fields, hshape⟩
  exact ⟨fields, by simpa only [← hm.uvars, ← hm.nparams, ← hcname, ← hfindex, ← hfname] using hshape⟩

theorem CompletedRecursorPhasesResult.normalizedFamilyRigid
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (owner : Fin s.families.size) : H.outVEnv.Rigid s.families[owner].name := by
  rcases hm.family owner with ⟨family, hfamily, hname, _⟩
  rw [hname]
  exact H.familyRigid family hfamily

theorem CompletedRecursorPhasesResult.alignmentOfRealization
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    (hlevels : g.levels.length = s.uvars)
    (hrecursors : ∀ owner, H.outVEnv.constants (g.recursorName owner) = some (g.recursor owner).toVConstant)
    (hwf : ∀ index, (g.equation index).WF H.outVEnv)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.RecursorRealization g H.outVEnv owner rec) :
    RecursorAlignmentCore (H.outVEnv.addDefEqRules g.equations) rec := by
  rcases g.recursor_shape owner (hrecursors owner) with ⟨hshape⟩
  refine ⟨s.params.length, g.levels, VExpr.bvarRange s.params.length s.params.length, ?_, ?_⟩
  · have hshape' := VRecursorShape.mono (venv' := H.outVEnv.addDefEqRules g.equations)
      VEnv.addDefEqRules_le hshape
    rw [hr.numParams]
    simpa only [hr.name, hr.uvars, hr.numMotives, hr.numMinors,
      hr.numIndices, hr.major] using Nonempty.intro hshape'
  · intro rule hmem
    rcases Lean4Lean.List.Forall₂.forall_exists_r hr.rules rule hmem with ⟨index, hindex, hi⟩
    have howner : s.constructors[index].owner = owner := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp hindex).2
    have hind := H.normalizedIndexArity hm index
    rcases H.rawConstructorShape hm index with ⟨fields, ⟨hc⟩⟩
    have hfields := g.fieldCount_of_equation H.outVEnvWF index
      (hrecursors _) hc (H.normalizedFamilyRigid hm _) hind (hwf index)
    subst fields
    have hdf : (H.outVEnv.addDefEqRules g.equations).defeqs (g.equation index) :=
      VEnv.addDefEqRules_defeqs_iff.mpr (.inr (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩))
    refine ⟨g.equation index, ?_⟩
    refine { shape := ?_
             rhs := hi.rhs.mono VEnv.addDefEqRules_le
             ctor := ?_ }
    · rw [hr.numParams]
      simpa only [hr.name, hr.uvars, hr.numMotives, hr.numMinors,
        hr.numIndices, hi.ctor, hi.nfields, howner] using g.iota_shape index hdf hind
    · refine ⟨s.uvars, hlevels, ?_⟩
      have hc' := VConstructorShape.mono (venv' := H.outVEnv.addDefEqRules g.equations)
        VEnv.addDefEqRules_le hc
      simpa only [hi.ctor, hi.nfields, hr.numIndices, hr.major, howner] using
        Nonempty.intro hc'

/-- The installed header has the concrete inductive kind and the exact
constructor-name list retained by formation. -/
theorem CompletedRecursorPhasesResult.familyInfo
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    ∃ info : InductiveVal,
      outEnv.constants.find? family.name = some (.inductInfo info) ∧
      info.ctors = family.ctors.map VConstVal.name := by
  have hvalue : family.toVConstVal ∈ R.headerEntries.map Prod.snd := by
    rw [R.headerValues]
    exact List.mem_map.mpr ⟨family, hf, rfl⟩
  rcases List.mem_map.mp hvalue with ⟨entry, he, hvalue⟩
  have hall : entry ∈ R.headerEntries ++ R.constructorEntries ++ H.entries := by
    simp [he]
  have ha := H.staged.combinedAtomic
  have hwf := R.sourceContext.checking.tr.map_wf
  have houtWF := ha.targetMapWF hwf
  have hname : entry.1.name = family.name := by
    rw [ha.entryNames hall, hvalue]
  rcases R.headerSourceAligned with ⟨_, hheaders⟩
  rcases hheaders.originInfo he with ⟨info, _, hinfo⟩
  have hlookup := ha.findEntry hwf (info := entry.1) (value := entry.2) hall
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, hname, hinfo] at hlookup
  have hfresh := ha.entryFresh hwf (info := entry.1) (value := entry.2) hall
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hname] at hfresh
  rcases H.productionInductiveOrigins family.name info hlookup with hold |
      ⟨familyIdx, hinfoName, ⟨A⟩⟩
  · rw [hfresh] at hold
    cases hold
  · have hfamilyIdx := A.familyIdx_lt
    have hfamilyEq : decl.types[familyIdx] = family :=
      VInductDecl.type_eq_of_mem_name
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
        (List.getElem_mem A.familyIdx_lt) hf (A.name.symm.trans hinfoName.symm)
    refine ⟨info, hlookup, ?_⟩
    apply List.ext_getElem
    · simpa only [List.length_map, hfamilyEq] using A.constructors
    · intro i hi hi'
      have hiSrc : i < decl.types[familyIdx].ctors.length := by rw [← A.constructors]; exact hi
      rcases A.constructor i hiSrc with ⟨C⟩
      simpa only [List.getElem_map, hfamilyEq] using C.name

theorem CompletedRecursorPhasesResult.majorOfRealization
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) {g : s.Instance}
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.RecursorRealization g H.outVEnv owner rec) :
    ∃ info, outEnv.constants.find? rec.getMajorInduct = some (.inductInfo info) := by
  rcases hm.family owner with ⟨family, hfamily, hname, _⟩
  rcases H.familyInfo family hfamily with ⟨info, hinfo, _⟩
  exact ⟨info, by simpa only [hr.major, hname] using hinfo⟩

/-- K uses the shared normalized parameter telescope. The stored source
header and constructor need only be definitionally equal to those types. -/
theorem CompletedRecursorPhasesResult.kOfRealization
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.RecursorRealization g H.outVEnv owner rec) :
    KLikeRecursor outEnv.constants (H.outVEnv.addDefEqRules g.equations) rec := by
  intro hk
  rcases hr.k hk with ⟨hfamilies, hctors, hzero, hfields⟩
  let index : Fin s.constructors.size := ⟨0, by omega⟩
  have howner : s.constructors[index].owner = owner := by
    apply Fin.eq_of_val_eq
    have h1 := s.constructors[index].owner.isLt
    have h2 := owner.isLt
    omega
  have hctorList : s.constructors.toList = [s.constructors[index]] := by
    apply List.ext_getElem
    · simpa only [Array.length_toList, List.length_singleton] using hctors
    · intro i hi hi'
      have heq : i = 0 := by simpa using hi'
      subst i
      rfl
  have hfield : s.constructors[index].fields = [] :=
    hfields _ (List.getElem_mem (l := s.constructors.toList) index.isLt)
  rcases hm.family owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hftype, hfctors⟩
  have hsingle : (s.declarationFamily owner).ctors.map VConstVal.name =
      [s.constructors[index].name] := by
    have hownerVal : s.constructors[index].owner.val = owner.val := congrArg Fin.val howner
    simp only [InductiveSignature.declarationFamily, hctorList, List.filterMap_cons,
      List.filterMap_nil, if_pos hownerVal, List.map_cons, List.map_nil]
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily
      (by simpa only [howner] using hfctors) with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  rcases H.familyInfo family hfamily with ⟨info, hlookupInfo, hinfoCtors⟩
  refine ⟨info, s.constructors[index].name, ?_, ?_, ?_⟩
  · simpa only [hr.major, hfname] using hlookupInfo
  · exact hinfoCtors.trans (hfctors.symm.trans hsingle)
  · apply KLikeAlignment.mono VEnv.addDefEqRules_le
    have henv := H.outVEnvWF
    have hlookupF := H.familyConstant family hfamily
    have hlookupC := H.constructorConstant ctor (List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩)
    have hfamilyWF : H.outVEnv.IsType s.uvars [] family.type := by
      simpa only [VConstant.WF, ← hfuvars] using henv.ordered.constWF hlookupF
    have hnormalized : H.outVEnv.IsDefEqU s.uvars [] family.type
        (VExpr.wrapForalls (s.params ++ s.families[owner].indices)
          (.sort s.families[owner].resultLevel)) := by
      simpa only [← hm.uvars] using hftype.symm.mono H.sourceLE
    have hnormalizedWF := hfamilyWF.defeqU_l henv (by trivial) hnormalized
    rcases VEnv.IsType.wrapForalls_inv henv (by trivial) hnormalizedWF with ⟨hctx, hbodyWF⟩
    have hsort : H.outVEnv.IsDefEq s.uvars
        ((s.params ++ s.families[owner].indices).reverse ++ [])
        (.sort s.families[owner].resultLevel) (.sort .zero)
        (.sort (.succ s.families[owner].resultLevel)) :=
      .sortDF (hbodyWF.sort_inv henv.ordered) trivial hzero
    rcases VExpr.wrapForalls_defeq hctx hsort with ⟨sortLevel, hwrapped⟩
    have hprop : H.outVEnv.IsDefEqU s.uvars [] family.type
        (VExpr.wrapForalls (s.params ++ s.families[owner].indices) (.sort .zero)) :=
      hnormalized.trans henv (by trivial) ⟨.sort sortLevel, hwrapped⟩
    let ctorBody := s.familyApp s.constructors[index].owner (VLevel.params s.uvars)
      (InductiveSignature.vars s.params.length 0) s.constructors[index].indices
    have hctorEq : H.outVEnv.IsDefEqU s.uvars [] ctor.type
        (VExpr.wrapForalls s.params ctorBody) := by
      simpa only [← hm.uvars, InductiveSignature.constructorType, InductiveSignature.fieldTypes,
        hfield, List.zipIdx_nil, List.map_nil, List.append_nil, List.length_nil] using
        hctype.symm.mono H.headerLE
    refine ⟨s.uvars, family.type, ctor.type, s.params ++ s.families[owner].indices,
      s.params, ctorBody, ?_, hprop, ?_, ?_, hctorEq, ?_, ?_⟩
    · change H.outVEnv.constants rec.getMajorInduct = some ⟨s.uvars, family.type⟩
      simpa only [hr.major, hfname, hfuvars] using hlookupF
    · rw [hr.numParams, hr.numIndices, List.length_append]
    · change H.outVEnv.constants s.constructors[index].name = some ⟨s.uvars, ctor.type⟩
      simpa only [hcname, hcuvars] using hlookupC
    · exact hr.numParams.symm
    · intro k hk hk'
      rcases hctx.reverse_getElem k hk with ⟨level, htype⟩
      refine ⟨.sort level, ?_⟩
      simpa only [VEnv.HasType, List.append_nil, List.getElem_append_left hk'] using htype

end VerifyInductive
end Lean4Lean
