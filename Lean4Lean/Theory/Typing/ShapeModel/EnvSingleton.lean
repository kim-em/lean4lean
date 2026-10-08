import Lean4Lean.Theory.Typing.ShapeModel.EnvArity
import Lean4Lean.Theory.Typing.NativeSingletonSourceFields

/-!
# Singleton elimination for propositional native equations (M4a, T6)

For an installed native equation whose major family is a proposition at the equation's levels
and whose recursor target level is not `≈ 0`, admissibility of the compiled block can only hold
through its singleton-elimination branch. That branch is certified in the compilation's header
environment `E = base.addConstVals source.typeConstants`: the compilation base extended by the
source family headers only, strictly before the block's constructors, recursors and equations.
This is the environment in which the equation's source is formed in the equation stratification
(`Ordered.equationStratification`, Theory/Typing/EquationStratification.lean): every stratum of a
native equation lies below its own installation, which starts from the installation base and
adds the headers first.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature InductiveSignature.NativeRecursorData

variable {env : VEnv}

/-- T6. `E` is the installation's header environment (the installation base extended by the
block's family headers; it contains the compilation's header environment, where admissibility is
certified). It is ordered, lies below `env`, and does not contain the equation (whose head, the
recursor, is not even declared in it). The family is the only one of its block, it has exactly one
constructor (the equation's), restoration is the identity, and every field of that constructor
that does not occur as a literal index is a proof in `E` (typed at `.sort .zero` in the context
of the parameters and the earlier fields, at the equation's levels). -/
theorem native_singleton (H : env.WF) {data : NativeRecursorData}
    (hd : (envTables env).natives n = some data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df)
    (hprop : data.schema.signature.families[data.owner].resultLevel.inst data.levels ≈ .zero)
    (htarget : ¬ data.target ≈ .zero) :
    ∃ E : VEnv, E ≤ env ∧ E.Ordered ∧ ¬ E.defeqs df ∧
      VDefEq.head df = .const data.name (VLevel.params data.uvars) ∧
      data.schema.signature.SingletonElimination E data.uvars data.levels ∧
      data.schema.signature.families.size = 1 ∧
      data.schema.signature.constructors.size = 1 ∧
      data.schema.restoration = {} ∧
      ∀ i (hi : i < data.schema.signature.constructors[index].fields.length),
        E.HasType data.uvars
          ((((data.schema.signature.fieldTypes data.schema.signature.constructors[index]).take i).map
              (·.instL data.levels)).reverse ++
            (data.schema.signature.params.map (·.instL data.levels)).reverse)
          ((data.schema.signature.fieldType i
            data.schema.signature.constructors[index].fields[i]).instL data.levels) (.sort .zero) ∨
        VExpr.bvar (data.schema.signature.constructors[index].fields.length - 1 - i) ∈
          data.schema.signature.constructors[index].indices := by
  have HT := envTables_inv H
  have hhead := native_head HT hd howner hgen
  obtain ⟨_, he⟩ := HT.natives hd
  obtain ⟨base, installBase, source, expanded, aux, block, installed, hdata, _, hbase, hr, _,
    hinst, hle, hIB, hblockWF, _⟩ := he
  obtain ⟨E, hE, hadm⟩ := hdata.admissible
  -- singleton branch of admissibility
  have hsing : data.schema.signature.SingletonElimination E data.uvars data.levels := by
    rcases hadm.elimination with hnz | ht | hsing
    · have hmem : data.schema.signature.families[data.owner] ∈
          data.schema.signature.families.toList := Array.getElem_mem_toList ..
      have := (hnz _ hmem).of_equiv hprop []
      exact absurd rfl this
    · exact absurd ht htarget
    · exact hsing.1
  -- one family: no auxiliaries, and the expanded headers are the source headers
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := hdata.correspondence
  have hlenFam := Lean4Lean.List.Forall₂.length_eq hfamilies
  have hlenDirect := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hdirect)
  have hsrcNe : source.types ≠ [] := hdata.sourceWF.1
  have hsrcPos : 0 < source.types.length := List.length_pos_iff.mpr hsrcNe
  have hdeclLen : data.schema.signature.declaration.types.length =
      data.schema.signature.families.size := by simp [declaration]
  rw [hdeclLen, hsing.1, List.length_append] at hlenFam
  have hauxNil : aux = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hsrcLen : source.types.length = 1 := by omega
  have hexpLen : expanded.types.length = 1 := by
    have := Lean4Lean.List.Forall₂.length_eq hdata.model.families
    rw [hdeclLen, hsing.1] at this
    exact this.symm
  have hheaders : source.typeConstants = expanded.typeConstants := by
    rw [hdata.headerPrefix, List.take_of_length_le]
    simp [VInductDecl.typeConstants, hexpLen, hsrcLen]
  rw [← hheaders] at hE
  -- `E` lies below the installed constructors
  obtain ⟨envTypes', envCtors, envRecs, htypes', hctors', hrecs', hinstEq⟩ := install_parts hinst
  let envP := (envCtors.addEliminators block.eliminators).addProjections block.projections
  have hPle : installBase ≤ envP :=
    (VEnv.addConstVals_le htypes').trans
      ((VEnv.addConstVals_le hctors').trans VEnv.addEliminators_addProjections_le)
  have hEP : E ≤ envP := by
    refine addConstVals_le_of hE (hbase.trans hPle) (fun ci hci => ?_)
    rw [← hdata.types] at hci
    rw [VEnv.addProjections_constants, VEnv.addEliminators_constants]
    exact (VEnv.addConstVals_le hctors').constants (VEnv.addConstVals_get htypes' hci)
  have hPinst : envP ≤ installed := by
    rw [hinstEq]; exact (VEnv.addConstVals_le hrecs').trans VEnv.addDefEqRules_le
  -- the recursor is fresh in the installation base
  have hentry : NativeRecursorData.ofInstance default
      (CaseSchema.ofCompilation source data.schema.signature aux) data.nativeInstance data.owner ∈
        NativeRecursorData.compilationEntries default source data.schema.signature aux
          data.nativeInstance :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  have hname : (NativeRecursorData.ofInstance default
      (CaseSchema.ofCompilation source data.schema.signature aux) data.nativeInstance
        data.owner).name = data.name := by
    simp only [NativeRecursorData.name, NativeRecursorData.ofInstance, CaseSchema.ofCompilation, hr]
  have hfresh := hdata.nativeEntries_fresh hinst hentry
  rw [hname] at hfresh
  have hctorSize : data.schema.signature.constructors.size = 1 := by
    have := hsing.2.1
    have := index.isLt
    omega
  -- the ordered header environment of the installation
  have hET : E ≤ envTypes' := by
    refine addConstVals_le_of hE (hbase.trans (VEnv.addConstVals_le htypes')) (fun ci hci => ?_)
    rw [← hdata.types] at hci
    exact VEnv.addConstVals_get htypes' hci
  have hTP : envTypes' ≤ envP :=
    (VEnv.addConstVals_le hctors').trans VEnv.addEliminators_addProjections_le
  obtain ⟨_, _, _, _, _, _, htypesWF, _⟩ := hblockWF
  have hord : envTypes'.Ordered := VEnv.Ordered.addConstVals hIB.ordered htypesWF htypes'
  have hsing' : data.schema.signature.SingletonElimination envTypes' data.uvars data.levels :=
    ⟨hsing.1, hsing.2.1, fun ctor hc i hi => (hsing.2.2 ctor hc i hi).imp (·.mono hET) id⟩
  refine ⟨envTypes', hTP.trans (hPinst.trans hle), hord, ?_, hhead, hsing', hsing.1, hctorSize,
    ?_, ?_⟩
  · intro hmem
    exact hIB.ordered.rigid_of_absent hfresh df
      (by rwa [VEnv.addConstVals_defeqs htypes'] at hmem) _ hhead
  · rw [hr, hauxNil]; rfl
  · intro i hi
    exact hsing'.2.2 _ (Array.getElem_mem_toList ..) i hi

/-- With an ordered installation base (true for the actual installation step of a well-formed
history), the equation is not stored in its header environment. -/
theorem native_singleton_not_mem {E installBase : VEnv} (hord : installBase.Ordered)
    (hsub : ∀ df', E.defeqs df' → installBase.defeqs df')
    {head : Name} (hfresh : installBase.constants head = none)
    (hhead : VDefEq.head df = .const head ls) : ¬ E.defeqs df := fun h =>
  hord.rigid_of_absent hfresh df (hsub df h) ls hhead

/-- Packaged with the saturated reconstruction program: every proof instruction of the
program at an occurrence's universe packet is justified in the header environment. -/
theorem native_singleton_proofField (H : env.WF) {data : NativeRecursorData}
    (hd : (envTables env).natives n = some data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df)
    (hprop : data.schema.signature.families[data.owner].resultLevel.inst data.levels ≈ .zero)
    (htarget : ¬ data.target ≈ .zero) :
    ∃ E : VEnv, E ≤ env ∧ ¬ E.defeqs df ∧ ∀ {program : SaturatedProgram data} {U : Nat}
      {levels : List VLevel} {arguments : List VExpr}, (∀ level ∈ levels, level.WF U) →
      data.saturatedProgram levels arguments = some program →
      ∀ {field : Nat} {domain : VExpr}, program.instructions[field]? = some (.proof domain) →
        E.HasType U (((program.equationBody.domains.take (data.indexOffset + field)).map
          (·.instL levels)).reverse) domain (.sort .zero) := by
  obtain ⟨E, hEle, hord, hnot, _, hsing, _, _, hid, _⟩ :=
    native_singleton H hd howner hgen hprop htarget
  exact ⟨E, hEle, hnot, fun hlev hsel _ _ hinstr =>
    data.saturatedProgram_proofField_inst hord hid hsing hlev hsel hinstr⟩

end Lean4Lean.ShapeModel
