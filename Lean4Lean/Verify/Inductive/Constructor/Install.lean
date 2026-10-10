import Lean4Lean.Verify.Inductive.Constructor.Environment

/-! # The constructor environment

`CtorInstall` collects what the constructor phase knows once the constructors are checked and
declared: the header environment `H`, the constructor check `K`, and the effect of
`declareConstructors` on the constant map. From it this file builds the abstract constructor
environment (`ctorVEnv`), the translation of the kernel constructors, and the checking
invariant of the constructor environment with the declaration's projection entries. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem VEnv.exists_addConstVals {env : VEnv} : ∀ {cis : List VConstVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConstVals cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConstVals (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConstVals, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VExpr.piArity_eq_forallArity : ∀ e : VExpr, e.piArity = e.forallArity
  | .forallE _ b => by simp [VExpr.piArity, VExpr.forallArity, VExpr.piArity_eq_forallArity b]
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .proj _ _ _ => rfl

theorem inductiveTypeInfos_size {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} (h : stats.nindices.size = indTypes.size)
    (nparams numNested : Nat) (isUnsafe : Bool) (lparams : List Name) :
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe lparams).size =
      indTypes.size := by
  simp [AddInductive.inductiveTypeInfos, h]

theorem inductiveTypeInfos_getElem {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams numNested : Nat} {isUnsafe : Bool}
    {lparams : List Name} (i : Nat)
    (hi : i < (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams).size) :
    let info := (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams)[i]
    ∃ (hi' : i < indTypes.size) (hn : i < stats.nindices.size),
      info.name = indTypes[i].name ∧ info.type = indTypes[i].type ∧
      info.numParams = nparams ∧ info.numIndices = stats.nindices[i] ∧
      info.all = (indTypes.map (·.name)).toList ∧ info.isUnsafe = isUnsafe ∧
      info.levelParams = lparams ∧ info.ctors = indTypes[i].ctors.map (·.name) := by
  have h1 : i < indTypes.size := by
    have := hi; simp [AddInductive.inductiveTypeInfos] at this; omega
  have h2 : i < stats.nindices.size := by
    have := hi; simp [AddInductive.inductiveTypeInfos] at this; omega
  exact ⟨h1, h2, by simp [AddInductive.inductiveTypeInfos]⟩

/-- What the constructor phase knows once the constructors are checked and declared. -/
structure CtorInstall (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (headerEnv ctorEnv : Environment)
    (classes : List (List (List Bool))) where
  H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv
  K : ConstructorsChecked H classes
  map_eq : ctorEnv.constants = insertConsts headerEnv.constants
    ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map .ctorInfo)
  quotInit_eq : ctorEnv.quotInit = headerEnv.quotInit
  fresh : ∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
    headerEnv.find? cval.name = none
  nodup : ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name)).Nodup
  nprim : ∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
    ¬ Kernel.Environment.primitives.contains cval.name
  nindices_size : stats.nindices.size = indTypes.size
  nindices : ∀ i (hi : i < decl.types.length) (hn : i < stats.nindices.size),
    stats.nindices[i] = decl.types[i].numIndices
  params_size : stats.params.size = nparams
  visible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe)

theorem trSourceConst_names {env : VEnv} {lparams : List Name} :
    ∀ {ctors : List Constructor} {ctors' : List VConstVal},
    List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
      TrSourceConst env lparams ctor.name ctor.type ctor') ctors ctors' →
    ctors.map (·.name) = ctors'.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [h.name, trSourceConst_names hs]

theorem constructorArity_instantiate1'_fvar (fv : FVarId) : ∀ (e : Expr) (d : Nat),
    AddInductive.constructorArity (e.instantiate1' (.fvar fv) d) = AddInductive.constructorArity e
  | .forallE _ _ b _, d => by
    simp [Expr.instantiate1', AddInductive.constructorArity, constructorArity_instantiate1'_fvar fv b]
  | .bvar i, d => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · simp [Expr.liftLooseBVars', AddInductive.constructorArity]
      · rfl
  | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl
  | .mdata .., _ | .proj .., _ | .app .., _ | .lam .., _ | .letE .., _ => rfl

theorem ParameterPrefix.constructorArity {stats : AddInductive.InductiveStats}
    (H : ParameterPrefix stats i source tail)
    (hfv : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv) :
    i ≤ stats.params.size ∧ AddInductive.constructorArity source =
      stats.params.size - i + AddInductive.constructorArity tail := by
  induction H with
  | done hi => subst hi; simp
  | @step i param body tail name dom bi hparam _ ih =>
    have hi : i < stats.params.size := (Array.getElem?_eq_some_iff.mp hparam).1
    obtain ⟨fv, rfl⟩ := hfv param (Array.mem_of_getElem? hparam)
    obtain ⟨-, ih⟩ := ih
    rw [Expr.instantiate1_eq, constructorArity_instantiate1'_fvar] at ih
    refine ⟨Nat.le_of_lt hi, ?_⟩
    simp only [AddInductive.constructorArity, ih]
    omega

theorem ConstantInfo.ctorInfo_safety (v : ConstructorVal) :
    (ConstantInfo.ctorInfo v).safety =
      if v.isUnsafe then DefinitionSafety.unsafe else .safe := by
  simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  by_cases h : v.isUnsafe = true <;> simp [h]

namespace CtorInstall

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {headerEnv ctorEnv : Environment} {classes : List (List (List Bool))}
  (I : CtorInstall c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv ctorEnv
    classes)
include I

/-- The abstract header environment. -/
abbrev headerVEnv : VEnv := I.H.context.venv

theorem headerVEnv_wf : I.headerVEnv.WF := I.H.context.wf

theorem sourceEnv_wf : sourceEnv.WF := by
  rw [← I.H.sourceContextVEnv]; exact I.H.sourceContext.wf

theorem sourceLE : sourceEnv ≤ I.headerVEnv := VEnv.addConstVals_le I.H.typesAdded

theorem types_length : indTypes.size = decl.types.length := by
  simpa using List.Forall₂.length_eq I.H.trSources

theorem infos_length : I.H.infos.length = indTypes.size := by
  rw [I.H.infos_eq]; simp [inductiveTypeInfos_size I.nindices_size]

/-- The kernel constructors of each family, with their abstract constructors. -/
theorem ctorTrAt (i : Nat) (hi : i < indTypes.size) :
    ∃ hi' : i < decl.types.length,
      List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
        TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
        indTypes[i].ctors decl.types[i].ctors := by
  have hi' : i < decl.types.length := I.types_length ▸ hi
  refine ⟨hi', ?_⟩
  have := List.forall₂_getElem I.K.ctorTr i (by simpa using hi) hi'
  simpa using this

theorem ctorNames : decl.constructorConstants.map (·.name) =
    (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
  rw [ctorInfos_names]
  simp only [VInductDecl.constructorConstants, List.map_flatMap]
  have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
        List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
          source.ctors target.ctors) sources targets →
      targets.flatMap (fun t => t.ctors.map (·.name)) =
        sources.flatMap (fun t => t.ctors.map (·.name)) := by
    intro sources targets h
    induction h with
    | nil => rfl
    | @cons s t ss ts hst _ ih =>
      simp only [List.flatMap_cons, ih]
      congr 1
      exact (trSourceConst_names hst).symm
  exact go I.K.ctorTr

theorem ctorNames_nodup : (decl.constructorConstants.map (·.name)).Nodup := by
  rw [I.ctorNames]; exact I.nodup

/-- A name of the abstract header environment is a name of the kernel header environment. -/
theorem headerFind_of_constants {n : Name} {ci : VConstant}
    (h : I.headerVEnv.constants n = some ci) : ∃ found, headerEnv.find? n = some found := by
  obtain ⟨found, hfound, -⟩ := I.H.context.checking.tr.find?_iff.mpr ⟨ci, h⟩
  exact ⟨found, hfound⟩

theorem ctorFresh : ∀ ci ∈ decl.constructorConstants, I.headerVEnv.constants ci.name = none := by
  intro ci hci
  cases h : I.headerVEnv.constants ci.name with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨found, hfound⟩ := I.headerFind_of_constants h
    have hmem : ci.name ∈ (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
      rw [← I.ctorNames]; exact List.mem_map_of_mem hci
    obtain ⟨cval, hcval, he⟩ := List.mem_map.mp hmem
    have := I.fresh cval hcval
    rw [he, hfound] at this; cases this

theorem exists_ctorVEnv : ∃ ctorVEnv, I.headerVEnv.addConstVals decl.constructorConstants =
    some ctorVEnv :=
  VEnv.exists_addConstVals I.ctorFresh I.ctorNames_nodup

/-- The abstract constructor environment. -/
noncomputable def ctorVEnv : VEnv := Classical.choose I.exists_ctorVEnv

theorem ctorsAdded : I.headerVEnv.addConstVals decl.constructorConstants = some I.ctorVEnv :=
  Classical.choose_spec I.exists_ctorVEnv

theorem headerLE : I.headerVEnv ≤ I.ctorVEnv := VEnv.addConstVals_le I.ctorsAdded

theorem constructorUvars : ∀ ci ∈ decl.constructorConstants, ci.uvars = decl.uvars := by
  intro ci hci
  obtain ⟨t, ht, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨s, hs, hst⟩ := List.Forall₂.forall_exists_r I.K.ctorTr t ht
  obtain ⟨sc, _, htr⟩ := List.Forall₂.forall_exists_r hst ci hci
  exact htr.uvars.trans I.H.uvars.symm

theorem ctorsWF' : ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF I.headerVEnv := by
  intro ci hci
  have := I.K.types ci hci
  simpa [VConstant.WF, VConstVal.toVConstant, I.constructorUvars ci hci] using this

/-- The core translation of the declaration. -/
theorem core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
    I.headerVEnv I.ctorVEnv := by
  refine TrInductDeclCore.ofPhases ⟨I.H.uvars, I.H.nparams, I.H.isUnsafe, I.H.typesAdded, ?_⟩
    ⟨I.ctorsAdded, I.K.ctorTr⟩
  have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
        TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
        source.ctors.map (·.name) = t.ctors.map (·.name)) sources targets →
      List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
        List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
          source.ctors target.ctors) sources targets →
      List.Forall₂ (TrInductiveTypeHeaders sourceEnv I.headerVEnv c.lparams) sources targets := by
    intro sources targets h1 h2
    induction h1 with
    | nil => exact .nil
    | cons h _ ih =>
      cases h2 with
      | cons h2 h2s => exact .cons ⟨h.1, List.Forall₂.imp (fun _ _ h => h.raw) h2⟩ (ih h2s)
  exact go I.H.trSources I.K.ctorTr

/-- The formation certificate of the declaration. -/
def formation : FormationCertificate sourceEnv decl where
  headers := I.H.headers
  envTypes := I.headerVEnv
  typesInstalled := I.H.typesAdded
  constructorParameters := I.K.parameterShapes
  constructors := I.K.shapes
  rawShapes := I.K.rawShapes

/-- The kernel headers with their constructors, in block order. -/
def ivals : List (InductiveVal × List ConstructorVal) :=
  (I.H.infos.zip indTypes.toList).map fun p => (p.1, familyCtorInfos stats c.lparams isUnsafe p.2)

theorem ivals_infos : I.ivals.map (·.1) = I.H.infos := by
  simp only [ivals, List.map_map]
  have : I.H.infos.length ≤ indTypes.toList.length := by simp [I.infos_length]
  simpa [Function.comp_def] using List.map_fst_zip this

theorem ivals_flat : I.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo) =
    (ctorInfos stats c.lparams isUnsafe indTypes.toList).map ConstantInfo.ctorInfo := by
  simp only [ivals, ctorInfos, List.map_flatMap, List.flatMap_map]
  have : indTypes.toList.length ≤ I.H.infos.length := by simp [I.infos_length]
  conv => rhs; rw [← List.map_snd_zip this]
  simp [List.flatMap_map]

theorem ivals_length : I.ivals.length = decl.types.length := by
  simp [ivals, I.infos_length, I.types_length]

theorem ivals_getElem (i : Nat) (hi : i < I.ivals.length) :
    ∃ (h1 : i < I.H.infos.length) (h2 : i < indTypes.size),
      I.ivals[i] = (I.H.infos[i], familyCtorInfos stats c.lparams isUnsafe indTypes[i]) := by
  have h1 : i < I.H.infos.length := by simp [ivals] at hi; omega
  have h2 : i < indTypes.size := by simpa [I.infos_length] using h1
  exact ⟨h1, h2, by simp [ivals]⟩

/-- The kernel constructor values all carry the declaration's parameter count. -/
theorem ctor_numParams : ∀ iv ∈ I.ivals, ∀ cval ∈ iv.2, cval.numParams = decl.nparams := by
  intro iv hiv cval hcval
  obtain ⟨⟨info, t⟩, _, rfl⟩ := List.mem_map.mp hiv
  obtain ⟨k, ctor, _, rfl⟩ := mem_ctorInfosFrom hcval
  simp [AddInductive.constructorInfo, I.params_size, I.H.nparams]

/-- One kernel constructor translates to its abstract constructor, with the arity
`numParams + numFields` of the abstract type. -/
theorem ctorAt (i : Nat) (hi : i < indTypes.size) (j : Nat)
    (hj : j < indTypes[i].ctors.length) (ctor' : VConstVal)
    (htr : TrSourceConst I.headerVEnv c.lparams indTypes[i].ctors[j].name
      indTypes[i].ctors[j].type ctor') :
    let cval := AddInductive.constructorInfo stats c.lparams isUnsafe indTypes[i] j
      indTypes[i].ctors[j]
    TrConstVal c.safety I.headerVEnv (.ctorInfo cval) ctor' ∧
      cval.numParams + cval.numFields = ctor'.type.piArity := by
  intro cval
  refine ⟨⟨⟨?_, ?_, ?_⟩, htr.name.symm⟩, ?_⟩
  · rw [ConstantInfo.ctorInfo_safety]
    simpa [cval, AddInductive.constructorInfo] using I.visible
  · exact htr.uvars.symm
  · exact htr.type
  · obtain ⟨tail, hprefix⟩ := I.K.parameterPrefixes.replay i hi j hj
    obtain ⟨k, hspine⟩ := I.K.parameterPrefixes.spines i hi j hj
    obtain ⟨-, harity⟩ := hprefix.constructorArity I.H.parameters.paramFVars
    have hk := hspine.constructorArity
    have hfa := TrExprS.forallArity_of_spine hspine htr.type
    rw [VExpr.piArity_eq_forallArity, hfa]
    simp only [cval, AddInductive.constructorInfo_numFields]
    simp only [AddInductive.constructorInfo]
    omega

/-- The kernel families with their constructors translate to the declaration's families. -/
theorem trTypes : List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
    TrIndType c.safety sourceEnv I.headerVEnv iv.1 iv.2 t) I.ivals decl.types := by
  apply List.forall₂_of_getElem I.ivals_length
  intro i hi hi'
  obtain ⟨h1, h2, heq⟩ := I.ivals_getElem i hi
  rw [heq]
  have hhdr := List.forall₂_getElem I.H.trHeaders i h1 hi'
  obtain ⟨_, hctors⟩ := I.ctorTrAt i h2
  refine ⟨hhdr.1, ?_, ?_⟩
  · rw [hhdr.2]
    rw [← trSourceConst_names hctors]
    simp [familyCtorInfos, ctorInfosFrom_names]
  · apply List.forall₂_of_getElem (by rw [familyCtorInfos_length]; exact List.Forall₂.length_eq hctors)
    intro j hj hj'
    have hjs : j < indTypes[i].ctors.length := by simpa [familyCtorInfos_length] using hj
    rw [familyCtorInfos_getElem]
    exact I.ctorAt i h2 j hjs _ (List.forall₂_getElem hctors j hjs hj')

end CtorInstall

end VerifyInductive
end Lean4Lean
