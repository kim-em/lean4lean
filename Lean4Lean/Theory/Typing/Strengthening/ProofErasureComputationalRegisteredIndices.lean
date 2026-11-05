import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalProjectionStage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalIndexFormation

/-! # Generic data-domain chains from earlier pattern coverage

The recursor's formation judgment predates its rules. It supplies computational
constructor-index typings under coverage of the previous registry, which then
supply all generic data-domain chains without assuming current completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- The selected registered singleton's generic constructor indices retain
computational typing certificates obtained before its rules were installed.
Only coverage of the previous pattern registry is assumed. -/
theorem registered_singleton_computational_indices_of_stage {rec : VRecursor}
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hAt : RecursorRegisteredAt env data decl env₀ env₁)
    (hstage : env₀ ∈ env.stages) (hrec : rec ∈ decl.recs) (hname : rec.name = data.name)
    (hcov : ∀ {p r}, env₀.pats p r → ComputationalPatternCoverage EnvironmentCore.definitions p r)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst packed ≈ .zero)
    (hw : ∀ l ∈ packed, l.WF univs) (hlen : packed.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env packed = some S) (hEl : data.propElim packed = some El) :
    ComputationalTelInst EnvironmentCore.definitions (data.propParams packed ++ S.fields).reverse
      (data.propParams packed ++ S.indices)
      (PropElim.branchPa S (data.propParams packed) ++ El.ctorIndices) := by
  have F := RecursorData.singletonSignature hAt.registered hlarge hzero
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := index.isLt; omega
  have hsc : data.singletonCtor = some index := by
    unfold RecursorData.singletonCtor
    have hfr : List.finRange data.schema.signature.constructors.size = [index] := by
      apply List.ext_getElem (by simp [hcs])
      intro n h1 h2
      simp only [List.length_finRange, hcs] at h1
      simp only [List.getElem_finRange, List.getElem_singleton]
      ext; simp; omega
    rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using howner), List.filter_nil]
  let c := data.schema.signature.constructors[index]
  obtain ⟨E, g, hEW, hE, hpats, hu, hlevels, htarget, H⟩ :=
    registered_singleton_specialized_formation_before_rules hAt hstage hrec hname hlarge hzero hw hlen
  have harity : (g.ctorIndicesAt c).length = (g.indicesAt data.owner).length := by
    have := F.arity c (Array.getElem_mem_toList ..)
    change c.indices.length = data.schema.signature.families[c.owner].indices.length at this
    have ho : c.owner = data.owner := howner
    simpa only [Instance.ctorIndicesAt, Instance.indicesAt, List.length_map, ho] using this
  obtain ⟨_, HI⟩ := computational_indices_of_earlier_formation heq hcon hqpat hE hEW
    (fun hp => hcov (hpats ▸ hp)) g hu F.families hcs data.owner index rfl htarget H harity
  have hSL : data.singletonLayout env packed = some
      ((data.recursorInstance.singletonCast data.owner c (data.genericSorts env c)).instL packed) := by
    simp only [RecursorData.singletonLayout, RecursorData.singletonLayoutGeneric, hsc,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, c]
  have ES := Option.some.inj (hSL.symm.trans hS)
  have hP : data.propParams packed = g.params := by
    simp [RecursorData.propParams, Instance.params, hlevels, RecursorData.recursorInstance,
      List.map_map, Function.comp_def, VExpr.instL_instL]
  have hF : S.fields = g.fieldsAt c := by
    rw [← ES]
    simp [SingletonLayout.instL, Instance.singletonCast, Instance.fieldsAt, hlevels,
      RecursorData.recursorInstance, List.map_map, Function.comp_def, VExpr.instL_instL]
  have hI : S.indices = g.indicesAt data.owner := by
    rw [← ES]
    simp [SingletonLayout.instL, Instance.singletonCast, Instance.indicesAt, hlevels,
      RecursorData.recursorInstance, List.map_map, Function.comp_def, VExpr.instL_instL]
  obtain ⟨k, hk, _, hfree⟩ := F.free
  have htp : data.targetParam = some k := by simp [RecursorData.targetParam, hk]
  have hEL : data.propElim packed = some
      ((data.recursorInstance.specialize 0 (packed.set k .zero)).singletonElim data.owner c
        (.const data.name (packed.set k .zero))) := by
    simp only [RecursorData.propElim, htp, hsc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, c]
  have EE := Option.some.inj (hEL.symm.trans hEl)
  have hfreeL : data.levels.map (·.inst (packed.set k .zero)) = data.levels.map (·.inst packed) :=
    List.map_congr_left fun l hl => hfree l hl packed .zero
  have hCI : El.ctorIndices = g.ctorIndicesAt c := by
    rw [← EE]
    simp [Instance.singletonElim, Instance.ctorIndicesAt, Instance.specialize, hlevels,
      RecursorData.recursorInstance, hfreeL]
  simpa only [PropElim.branchPa, hP, hF, hI, hCI] using HI

/-- Earlier pattern coverage supplies all generic data-domain chains required
by the stored singleton equation. The ambient extraction well-formedness only
retags the chains at its chosen data-field universes. -/
theorem registered_singleton_data_domains_of_stage {rec : VRecursor}
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hAt : RecursorRegisteredAt env data decl env₀ env₁)
    (hstage : env₀ ∈ env.stages) (hrec : rec ∈ decl.recs) (hname : rec.name = data.name)
    (hcov : ∀ {p r}, env₀.pats p r → ComputationalPatternCoverage EnvironmentCore.definitions p r)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst packed ≈ .zero)
    (hw : ∀ l ∈ packed, l.WF univs) (hlen : packed.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env packed = some S) (hEl : data.propElim packed = some El) :
    SingletonGenericDataDomainChains EnvironmentCore.definitions S (data.propParams packed) El := by
  obtain ⟨S', El', hS', hEl', W⟩ := RecursorData.propElim_wf henv hAt.registered hlarge hzero hw hlen
    ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hEl'.symm.trans hEl)
  exact (registered_singleton_computational_indices_of_stage heq hcon hqpat hAt hstage hrec hname
    hcov hlarge hzero hw hlen howner hS hEl).generic_data_domains W

end Lean4Lean.VEnv.Strengthening
