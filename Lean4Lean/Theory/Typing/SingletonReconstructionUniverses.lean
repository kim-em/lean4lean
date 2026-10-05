import Lean4Lean.Theory.Inductive.ProjectionUniverseNaturality
import Lean4Lean.Theory.Inductive.SingletonReconstruction
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! The concrete singleton selector program commutes with universe
specialization. Literal field/index positions are unchanged. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

def ProjectionFunction.instL (fn : ProjectionFunction) (packed : List VLevel) : ProjectionFunction :=
  { targetLevel := fn.targetLevel.inst packed
    value := fn.value.instL packed
    type := fn.type.instL packed }

@[simp] theorem ProjectionData.fieldIndex_instL (data : ProjectionData) :
    (data.instL packed).fieldIndex field = data.fieldIndex field := by
  unfold ProjectionData.fieldIndex ProjectionData.instL
  simp only [List.length_map, List.zipIdx_map, List.find?_map, Option.map_map, Function.comp_def]
  congr 1
  congr 1
  funext pair
  rcases pair with ⟨e, i⟩
  cases e <;> rfl

private theorem vars_instL (n k : Nat) :
    (vars n k).map (VExpr.instL packed) = vars n k := by
  simp [vars, List.map_map, Function.comp_def, VExpr.instL]

theorem ProjectionData.arguments_instL (data : ProjectionData) :
    data.arguments.map (VExpr.instL packed) = (data.instL packed).arguments := by
  simp [ProjectionData.arguments, ProjectionData.instL, vars_instL, VExpr.instL]

theorem ProjectionData.fieldTarget_instL (data : ProjectionData) :
    (data.fieldTarget domain previous).instL packed =
      (data.instL packed).fieldTarget (domain.instL packed)
        (previous.map (ProjectionFunction.instL · packed)) := by
  simp only [ProjectionData.fieldTarget, instantiateParams_instL, List.map_append,
    vars_instL, List.map_map, Function.comp_def, VExpr.instL_mkApps,
    ProjectionData.arguments_instL, ProjectionFunction.instL, ProjectionData.instL,
    List.length_map]

theorem ProjectionData.indexSelector_instL (data : ProjectionData) :
    (data.indexSelector domain target previous index).instL packed =
      (data.instL packed).indexSelector (domain.instL packed) (target.inst packed)
        (previous.map (ProjectionFunction.instL · packed)) index := by
  simp only [ProjectionFunction.instL, ProjectionData.indexSelector,
    VExpr.instL_wrapLams, VExpr.instL_wrapForalls, ProjectionData.fieldTarget_instL,
    ProjectionData.instL, List.map_append, List.map_cons, List.map_nil,
    List.length_map, VExpr.instL]

theorem ProjectionData.proofSelector_instL (data : ProjectionData) :
    (data.proofSelector block owner levels domain previous).instL packed =
      (data.instL packed).proofSelector block owner (levels.map (·.inst packed))
        (domain.instL packed) (previous.map (ProjectionFunction.instL · packed)) := by
  simp only [ProjectionFunction.instL, ProjectionData.proofSelector,
    VExpr.instL_wrapLams, VExpr.instL_wrapForalls, ProjectionData.fieldTarget_instL,
    ProjectionData.instL, List.map_append, List.map_cons, List.map_nil,
    List.length_map, VExpr.instL_mkApps, VExpr.instL_liftN, vars_instL,
    VExpr.instL, VLevel.inst]

theorem ProjectionData.reconstructionPrefix_instL (data : ProjectionData)
    {domains : List VExpr} {targets : List VLevel} {previous output : List ProjectionFunction}
    (H : data.reconstructionPrefix block owner levels domains targets previous = some output) :
    (data.instL packed).reconstructionPrefix block owner (levels.map (·.inst packed))
      (domains.map (VExpr.instL packed)) (targets.map (·.inst packed))
      (previous.map (ProjectionFunction.instL · packed)) =
        some (output.map (ProjectionFunction.instL · packed)) := by
  induction targets generalizing domains previous with
  | nil => cases domains with
    | nil => cases H; rfl
    | cons d ds => cases H
  | cons target targets ih =>
    cases domains with
    | nil => cases H
    | cons domain domains =>
      simp only [ProjectionData.reconstructionPrefix] at H
      simp only [List.map_cons, ProjectionData.reconstructionPrefix, List.length_map,
        ProjectionData.fieldIndex_instL]
      split at H
      · rename_i index hindex
        split at H <;> try contradiction
        rename_i hbound
        simp only [ProjectionData.instL, List.length_map, if_pos hbound]
        have hh := ih H
        simpa only [bind, Option.bind_some, List.map_append, List.map_cons, List.map_nil,
          ProjectionData.indexSelector_instL, ProjectionData.instL] using hh
      · rename_i hindex
        cases target <;> try contradiction
        have hh := ih H
        simpa only [bind, Option.bind_some, VLevel.inst, List.map_append, List.map_cons, List.map_nil,
          ProjectionData.proofSelector_instL] using hh

theorem singletonReconstructAt_instL {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {params : List VExpr}
    (H : schema.singletonReconstructAt block owner U levels targets params indices major = some output)
    (hw : ∀ level ∈ packed, level.WF U') :
    schema.singletonReconstructAt block owner U' (levels.map (·.inst packed))
      (targets.map (·.inst packed)) (params.map (VExpr.instL packed))
      (indices.map (VExpr.instL packed)) (major.instL packed) = some (output.instL packed) := by
  unfold singletonReconstructAt at H ⊢
  split at H <;> try contradiction
  have hlevels' : (levels.map (·.inst packed)).all (fun l => decide (l.WF U')) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_def, decide_eq_true_eq]
    exact fun _ _ => VLevel.WF.inst hw
  have htargets' : (targets.map (·.inst packed)).all (fun l => decide (l.WF U')) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_def, decide_eq_true_eq]
    exact fun _ _ => VLevel.WF.inst hw
  rw [hlevels', htargets']
  simp only [Bool.true_and, Bool.not_true, Bool.false_eq_true, if_false]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨data, hdata, H⟩ := H
  simp only [bind, projectionData_instL hdata, Option.bind_some, List.length_map,
    ProjectionData.instL]
  split at H <;> try contradiction
  rename_i harity
  rw [if_neg harity]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨fields, hfields, H⟩ := H
  cases H
  have hfields' := data.reconstructionPrefix_instL (packed := packed) hfields
  simp only [ProjectionData.instL, List.map_nil] at hfields'
  rw [hfields']
  simp only [bind, Option.bind_some, Option.pure_def, Option.some.injEq,
    instantiateParams_instL, List.map_append, List.map_map, Function.comp_def,
    VExpr.instL_mkApps, List.map_cons, List.map_nil, ProjectionFunction.instL]

end Lean4Lean.InductiveSignature.CaseSchema
