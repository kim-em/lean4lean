import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation

/-! # Facts about a registered native large-eliminating proposition

A registered native recursor whose target universe can be large and whose source sort is
`Prop` at an occurrence comes from a singleton signature with identity restoration and a
free elimination universe (`Instance.FreeTarget`). -/

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
  · rw [hl]; exact hadm.levels_length

end InductiveSignature.NativeRecursorData
end Lean4Lean
