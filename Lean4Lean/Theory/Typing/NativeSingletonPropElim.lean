import Lean4Lean.Theory.Typing.SingletonExtraction
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.NativeMajorFamily
import Lean4Lean.Theory.Typing.NativeSingletonTyping

/-! # Singleton extraction for a registered native recursor

The abstract extraction interface (`PropElim`, `SingletonExtraction.lean`) is
instantiated at a registered native recursor of a large-eliminating inductive
proposition: the field and index telescopes come from the generated signature at the
occurrence's source universes, and the eliminator into `Prop` is the native recursor
itself with its free elimination universe (`Instance.FreeTarget`) set to zero. -/

namespace Lean4Lean
open VExpr InductiveSignature VEnv

namespace InductiveSignature.NativeRecursorData
variable {env : VEnv}

/-- What a registered native large-eliminating proposition provides: a singleton
signature, identity restoration, free elimination universe, and the installed
recursor typed by the generator. -/
structure SingletonFacts (env : VEnv) (data : NativeRecursorData) : Prop where
  families : data.schema.signature.families.size = 1
  constructors : data.schema.signature.constructors.size ≤ 1
  restoration : data.schema.restoration = {}
  free : ∃ k, data.target = .param k ∧ k < data.uvars ∧
    ∀ l ∈ data.levels, ∀ (ls : List VLevel) (u : VLevel), l.inst (ls.set k u) = l.inst ls
  levels_wf : ∀ l ∈ data.levels, l.WF data.uvars
  recursor : env.constants data.name =
    some { uvars := data.uvars, type := data.nativeInstance.recursorType data.owner }
  singleton : ∃ envTypes, envTypes ≤ env ∧
    data.schema.signature.SingletonElimination envTypes data.uvars data.levels
  familyHead : ∀ {U Γ levels}, env.WF → OnCtx Γ (env.IsType U) → (∀ l ∈ levels, l.WF U) →
    levels.length = data.schema.signature.uvars →
    ∃ domains level, env.HasType U Γ
      (.const data.schema.signature.families[data.owner].name levels)
      (VExpr.wrapForalls domains (.sort level)) ∧
      level ≈ data.schema.signature.families[data.owner].resultLevel.inst levels
  arity : ∀ ctor ∈ data.schema.signature.constructors.toList,
    ctor.indices.length = data.schema.signature.families[ctor.owner].indices.length
  uvars : data.levels.length = data.schema.signature.uvars

theorem singletonFacts (H : NativeRecursorRegistered env data) (hlarge : data.largeTarget = true)
    (hzero : data.sourceLevel packed ≈ .zero) : SingletonFacts env data := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, hbase, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.nativeInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [NativeRecursorData.nativeInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  obtain ⟨envTypes, htypes0, hadm⟩ := hdata.admissible
  have hsingle : data.schema.signature.SingletonElimination envTypes g.uvars g.levels ∧
      g.FreeTarget := by
    rcases hadm.elimination with hnz | hz | hs
    · exfalso
      have hfam := hnz _ (Array.getElem_mem_toList (i := data.owner.val) data.owner.isLt)
      unfold sourceLevel CaseSchema.sourceLevel at hzero
      rw [← hl] at hfam
      have h1 := (hfam.inst (ls := packed)) []
      have h2 := congrFun hzero []
      exact h1 (by simpa [VLevel.eval] using h2)
    · exfalso
      unfold largeTarget at hlarge
      rw [ht] at hlarge
      have := congrFun hz (List.replicate data.uvars 1)
      simp [VLevel.eval] at this
      simp [this] at hlarge
    · exact hs
  have hfam := hsingle.1.1
  have hrest : data.schema.restoration = {} := hr.trans (hdata.restoration_of_singleton hfam)
  -- the installed environment contains the checked headers
  have hinst := hi
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hinst
  obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
  have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
    (VEnv.addProjections_le.trans ((VEnv.addConstVals_le he3).trans
      (VEnv.addDefEqRules_le.trans he)))
  have hbaseLE : base ≤ env := hbase.trans ((VEnv.addConstVals_le he1).trans hle1)
  have htypesLE : envTypes ≤ env := by
    have he1' := he1
    rw [hdata.types, hdata.typeConstants_of_singleton hfam] at he1'
    exact (VEnv.addConstVals_mono hbase htypes0 he1').trans hle1
  refine {
    families := hfam
    constructors := hsingle.1.2.1
    restoration := hrest
    free := ?_
    levels_wf := by rw [hl, hu]; exact hadm.levels_wf
    recursor := ?_
    singleton := ?_
    familyHead := ?_
    arity := hdata.model.constructorArity
    uvars := ?_ }
  · obtain ⟨k, hk, hlv⟩ := hsingle.2
    have hwf := hadm.target_wf
    rw [hk] at hwf
    exact ⟨k, ht.trans hk, by rw [hu]; simpa [VLevel.WF] using hwf, by rw [hl]; exact hlv⟩
  · have hgen : data.recursorType = some (data.nativeInstance.recursorType data.owner) := by
      simp [recursorType, hrest]
    exact NativeRecursorRegistered.recursorType
      ⟨base, installBase, source, expanded, g, auxiliaries, block, _, hdata, ‹_›, hbase, hr, ‹_›,
        hu, hl, ht, hi, he⟩ hgen
  · exact ⟨envTypes, htypesLE, by rw [hu, hl]; exact hsingle.1⟩
  · intro U Γ levels henv hΓ hlevels hlen
    have hconstants : ∀ family ∈ source.types,
        env.constants family.name = some family.toVConstant := fun family hf =>
      he.constants (VInductBlock.install_type_lookup' hi (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨family, hf, rfl⟩))
    obtain ⟨domains, level, hH, hlevel⟩ :=
      hdata.family_head_type ‹_› henv hΓ hbaseLE hconstants data.owner hlevels hlen
    rw [hdata.restoration_of_singleton hfam] at hH
    exact ⟨domains, level, by simpa [Restoration.headName, Restoration.headLevels,
      Restoration.recursorName] using hH, hlevel⟩
  · rw [hl]; exact hadm.levels_length

/-- Universe instantiation of a cast specification. -/
def _root_.Lean4Lean.CastSpec.instL (S : CastSpec) (ls : List VLevel) : CastSpec where
  fields := S.fields.map (·.instL ls)
  indices := S.indices.map (·.instL ls)
  slot := S.slot
  sorts := S.sorts.map (·.inst ls)

/-- The free elimination universe parameter. -/
def targetParam (data : NativeRecursorData) : Option Nat :=
  match data.target with
  | .param k => some k
  | _ => none

/-- The owner's unique constructor. -/
def singletonCtor (data : NativeRecursorData) : Option (Fin data.schema.signature.constructors.size) :=
  match (List.finRange data.schema.signature.constructors.size).filter
      (fun i => data.schema.signature.constructors[i].owner == data.owner) with
  | [i] => some i
  | _ => none

/-- The sorts of the data fields, chosen at the generic universes. Proof fields get `Prop`. -/
noncomputable def genericSorts (env : VEnv) (data : NativeRecursorData)
    (c : Constructor data.schema.signature.families.size) : List VLevel :=
  (List.range (data.nativeInstance.sFields c).length).map fun i =>
    match fieldSlot (data.nativeInstance.sCtorIndices c) (data.nativeInstance.sFields c).length i with
    | some _ => Classical.epsilon fun u =>
      env.HasType data.uvars
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take i).reverse
        ((data.nativeInstance.sFields c).getD i default) (.sort u)
    | none => .zero

/-- The cast specification at the generic universes. -/
noncomputable def castSpecGeneric (env : VEnv) (data : NativeRecursorData) : Option CastSpec := do
  let i ← data.singletonCtor
  let c := data.schema.signature.constructors[i]
  return data.nativeInstance.singletonCast data.owner c (data.genericSorts env c)

/-- The cast specification at an occurrence's universes: the generic one, instantiated. -/
noncomputable def castSpec (env : VEnv) (data : NativeRecursorData) (packed : List VLevel) :
    Option CastSpec :=
  (data.castSpecGeneric env).map (·.instL packed)

/-- The parameter telescope at an occurrence's universes. -/
def propParams (data : NativeRecursorData) (packed : List VLevel) : List VExpr :=
  data.nativeInstance.params.map (·.instL packed)

/-- Elimination into `Prop` through the native recursor itself, at an occurrence's universes
with the free elimination universe set to zero. -/
def propElim (data : NativeRecursorData) (packed : List VLevel) : Option PropElim := do
  let k ← data.targetParam
  let i ← data.singletonCtor
  return (data.nativeInstance.specialize 0 (packed.set k .zero)).singletonElim data.owner
    data.schema.signature.constructors[i] (.const data.name (packed.set k .zero))

theorem propElim_wf (henv : env.WF) (H : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hpk : ∀ l ∈ packed, l.WF U) (hlen : packed.length = data.uvars)
    (hctor : ∃ i : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[i].owner = data.owner) :
    ∃ S E, data.castSpec env packed = some S ∧ data.propElim packed = some E ∧
      PropElim.WF S (data.propParams packed) E env U := by
  have F := singletonFacts H hlarge hzero
  obtain ⟨k, hk, hkU, hfree⟩ := F.free
  obtain ⟨i, hi⟩ := hctor
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := i.isLt; omega
  have hfam := F.families
  have htp : data.targetParam = some k := by simp [targetParam, hk]
  have hsc : data.singletonCtor = some i := by
    unfold singletonCtor
    have hfr : List.finRange data.schema.signature.constructors.size = [i] := by
      apply List.ext_getElem (by simp [hcs])
      intro n h1 h2
      simp only [List.length_finRange, hcs] at h1
      simp only [List.getElem_finRange, List.getElem_singleton]
      ext; simp; omega
    rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using hi), List.filter_nil]
  have hls0 : ∀ l ∈ packed.set k .zero, l.WF U := by
    intro l hl
    rcases List.mem_or_eq_of_mem_set hl with h | rfl
    · exact hpk l h
    · simp [VLevel.WF]
  have hlev : data.levels.map (·.inst (packed.set k .zero)) = data.levels.map (·.inst packed) :=
    List.map_congr_left fun l hl => hfree l hl packed .zero
  -- the instance at the occurrence, eliminating into `Prop`
  let gp := data.nativeInstance.specialize U (packed.set k .zero)
  have hgpl : gp.levels = data.levels.map (·.inst packed) := hlev
  have htarget : gp.targetLevel = .zero := by
    show (data.target).inst (packed.set k .zero) = .zero
    rw [hk]
    simp [VLevel.inst, List.getD_eq_getElem?_getD, List.getElem?_set_self, hlen, hkU]
  have hhead : env.HasType U [] (.const data.name (packed.set k .zero))
      (gp.recursorType data.owner) := by
    have := HasType.const (env := env) (Γ := []) F.recursor hls0 (by simp [hlen])
    rwa [Instance.recursorType_specialize _ U] at this
  obtain ⟨c, hc⟩ : ∃ c, data.schema.signature.constructors[i] = c := ⟨_, rfl⟩
  have hown : c.owner = data.owner := hc ▸ hi
  have hFeq : (data.nativeInstance.sFields c).map (·.instL packed) = gp.sFields c := by
    simp [gp, Instance.sFields, Instance.specialize, nativeInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hIeq : (data.nativeInstance.sIndices data.owner).map (·.instL packed) =
      gp.sIndices data.owner := by
    simp [gp, Instance.sIndices, Instance.specialize, nativeInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hCIeq : (data.nativeInstance.sCtorIndices c).map (·.instL packed) = gp.sCtorIndices c := by
    simp [gp, Instance.sCtorIndices, Instance.specialize, nativeInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hPeq : data.propParams packed = gp.params := by
    simp [gp, propParams, Instance.params, Instance.specialize, nativeInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hS : data.castSpec env packed = some (gp.singletonCast data.owner c
      ((data.genericSorts env c).map (·.inst packed))) := by
    simp only [castSpec, castSpecGeneric, hsc, hc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.map_some]
    simp only [CastSpec.instL, Instance.singletonCast, Option.some.injEq, CastSpec.mk.injEq]
    refine ⟨hFeq, hIeq, ?_, trivial⟩
    rw [← hFeq, ← hCIeq, List.length_map]
    congr 1; funext j; exact (fieldSlot_instL _ _ _ _).symm
  have hE : data.propElim packed = some (gp.singletonElim data.owner c
      (.const data.name (packed.set k .zero))) := by
    simp only [propElim, htp, hsc, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  refine ⟨_, _, hS, hE, ?_⟩
  rw [hPeq]
  have hmem : c ∈ data.schema.signature.constructors.toList := hc ▸ Array.getElem_mem_toList ..
  have hnf : (gp.sFields c).length = c.fields.length := by
    simp [Instance.sFields, fieldTypes]
  have hnfG : (data.nativeInstance.sFields c).length = c.fields.length := by
    simp [Instance.sFields, fieldTypes]
  have harity : (gp.sCtorIndices c).length = (gp.sIndices data.owner).length := by
    have := F.arity c hmem
    simp [Instance.sCtorIndices, Instance.sIndices, this, hown]
  have hlw : ∀ l ∈ gp.levels, l.WF U := by
    rw [hgpl]
    intro l hl
    obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hpk
  have hfamHead : ∀ {Γ}, OnCtx Γ (env.IsType gp.uvars) → ∃ domains level,
      env.HasType gp.uvars Γ (.const data.schema.signature.families[data.owner].name gp.levels)
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ .zero := by
    intro Γ hΓ
    obtain ⟨domains, level, hH, hlv⟩ := F.familyHead henv hΓ hlw
      (by rw [hgpl, List.length_map]; exact F.uvars)
    refine ⟨domains, level, hH, ?_⟩
    have e : data.schema.signature.families[data.owner].resultLevel.inst gp.levels =
        data.sourceLevel packed := by
      rw [hgpl]
      simp [sourceLevel, CaseSchema.sourceLevel, VLevel.inst_inst]
    rw [e] at hlv
    exact Eq.trans hlv hzero
  -- the generic instance, eliminating into `Prop`, for the choice of the data fields' sorts
  let gG := data.nativeInstance.specialize data.uvars ((VLevel.params data.uvars).set k .zero)
  have hgGl : gG.levels = data.levels := by
    show data.levels.map (·.inst ((VLevel.params data.uvars).set k .zero)) = data.levels
    conv => rhs; rw [← List.map_id data.levels]
    apply List.map_congr_left
    intro l hl
    rw [hfree l hl, VLevel.inst_id (F.levels_wf l hl)]
    rfl
  have hlsG : ∀ l ∈ (VLevel.params data.uvars).set k .zero, l.WF data.uvars := by
    intro l hl
    rcases List.mem_or_eq_of_mem_set hl with h | rfl
    · exact VLevel.params_wf h
    · simp [VLevel.WF]
  have htargetG : gG.targetLevel = .zero := by
    show (data.target).inst ((VLevel.params data.uvars).set k .zero) = .zero
    rw [hk]
    simp [VLevel.inst, List.getD_eq_getElem?_getD, hkU]
  have hheadG : env.HasType gG.uvars [] (.const data.name ((VLevel.params data.uvars).set k .zero))
      (gG.recursorType data.owner) := by
    have := HasType.const (env := env) (Γ := []) F.recursor hlsG (by simp)
    rwa [Instance.recursorType_specialize _ data.uvars] at this
  have hFG : gG.sFields c = data.nativeInstance.sFields c := by
    simp only [Instance.sFields, hgGl]; rfl
  have hPG : gG.params = data.nativeInstance.params := by
    simp only [Instance.params, hgGl]; rfl
  have harityG : (gG.sCtorIndices c).length = (gG.sIndices data.owner).length := by
    have := F.arity c hmem
    simp [Instance.sCtorIndices, Instance.sIndices, this, hown]
  have hctxG := gG.singleton_fieldsCtx henv hfam hcs data.owner i hc hown htargetG hheadG harityG
  rw [hFG, hPG] at hctxG
  have hspec : ∀ j (hj : j < (data.nativeInstance.sFields c).length) k',
      fieldSlot (data.nativeInstance.sCtorIndices c) (data.nativeInstance.sFields c).length j =
        some k' →
      env.HasType data.uvars
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse
        (data.nativeInstance.sFields c)[j] (.sort ((data.genericSorts env c).getD j .zero)) := by
    intro j hj k' hslot
    have hget : (data.genericSorts env c).getD j .zero = Classical.epsilon fun u =>
        env.HasType data.uvars
          (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse
          ((data.nativeInstance.sFields c).getD j default) (.sort u) := by
      simp [genericSorts, List.getD_eq_getElem?_getD, List.getElem?_range hj, hslot]
    have hex : ∃ u, env.HasType data.uvars
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse
        ((data.nativeInstance.sFields c).getD j default) (.sort u) := by
      have := hctxG (j + 1) hj
      rw [List.take_succ_eq_append_getElem hj, ← List.append_assoc, List.reverse_append] at this
      obtain ⟨_, u, hu⟩ := this
      exact ⟨u, by rw [getD_of_lt hj]; exact hu⟩
    have := Classical.epsilon_spec hex
    rw [hget, ← getD_of_lt (d := default) hj]
    exact this
  have hlift : ∀ j (hj : j < (data.nativeInstance.sFields c).length) (u : VLevel),
      env.HasType data.uvars
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse
        (data.nativeInstance.sFields c)[j] (.sort u) →
      env.HasType U (gp.params ++ (gp.sFields c).take j).reverse
        ((gp.sFields c)[j]'(by rw [hnf]; rw [hnfG] at hj; exact hj)) (.sort (u.inst packed)) := by
    intro j hj u h
    have h' := h.instL hpk
    have e1 : (List.map (VExpr.instL packed)
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse) =
        (gp.params ++ (gp.sFields c).take j).reverse := by
      rw [← hPeq, ← hFeq]
      simp [propParams, List.map_reverse, List.map_take]
    have e2 : (data.nativeInstance.sFields c)[j].instL packed = (gp.sFields c)[j]'(by
        rw [hnf]; rw [hnfG] at hj; exact hj) := by
      simp only [← hFeq, List.getElem_map]
    rw [e1, e2] at h'
    exact h'
  have hslotEq : ∀ j, fieldSlot (gp.sCtorIndices c) (gp.sFields c).length j =
      fieldSlot (data.nativeInstance.sCtorIndices c) (data.nativeInstance.sFields c).length j := by
    intro j
    rw [← hCIeq, ← hFeq, List.length_map, fieldSlot_instL]
  have hprop : ∀ j (hj : j < (gp.sFields c).length),
      fieldSlot (gp.sCtorIndices c) (gp.sFields c).length j = none →
      env.HasType gp.uvars (gp.params ++ (gp.sFields c).take j).reverse (gp.sFields c)[j]
        (.sort .zero) := by
    intro j hj hnone
    have hjc : j < c.fields.length := hnf ▸ hj
    obtain ⟨envTypes, hle, hsing⟩ := F.singleton
    rcases hsing.2.2 c hmem j hjc with hP | hbv
    · have hG : env.HasType data.uvars
          (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take j).reverse
          ((data.nativeInstance.sFields c)[j]'(hnfG ▸ hjc)) (.sort .zero) := by
        have := hP.mono hle
        simpa [Instance.sFields, Instance.params, nativeInstance, fieldTypes, List.map_take,
          List.reverse_append] using this
      exact hlift j (hnfG ▸ hjc) .zero hG
    · exfalso
      apply fieldSlot_none hnone
      rw [hnf]
      exact List.mem_map.2 ⟨_, hbv, rfl⟩
  have hsorts : ∀ j (hj : j < (gp.sFields c).length) k',
      fieldSlot (gp.sCtorIndices c) (gp.sFields c).length j = some k' →
      env.HasType gp.uvars (gp.params ++ (gp.sFields c).take j).reverse (gp.sFields c)[j]
        (.sort (((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero)) := by
    intro j hj k' hslot
    have hjG : j < (data.nativeInstance.sFields c).length := hnfG ▸ hnf ▸ hj
    rw [hslotEq] at hslot
    have := hlift j hjG _ (hspec j hjG k' hslot)
    have e : ((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero =
        ((data.genericSorts env c).getD j .zero).inst packed := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (data.genericSorts env c)[j]? <;> simp [VLevel.inst]
    rw [e]
    exact this
  have hsortWF : ∀ j, (((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero).WF gp.uvars := by
    intro j
    have e : ((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero =
        ((data.genericSorts env c).getD j .zero).inst packed := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (data.genericSorts env c)[j]? <;> simp [VLevel.inst]
    rw [e]
    exact VLevel.WF.inst hpk
  exact gp.singletonElim_wf henv hfam hcs data.owner i hc hown htarget hhead harity hfamHead
    hprop hsorts hsortWF

end InductiveSignature.NativeRecursorData
end Lean4Lean
