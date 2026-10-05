import Lean4Lean.Theory.Typing.CaseLevelEquiv
import Lean4Lean.Theory.Inductive.ProjectionProgramLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality

/-! Congruence of the actual projection generator. Universes of unused earlier
fields need not agree; complete case calls compare their typed motives. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
variable {input output : List VExpr} {fields fields' levels levels' : List VLevel}

private theorem shifted_levels_inst (hfields : fields.length = count)
    (hlevels : levels.length = n) :
    ((List.range n).map (fun i => VLevel.param (count + i))).map
      (·.inst (fields ++ levels)) = levels := by
  apply List.ext_get (by simp [hlevels])
  intro i hi hi'
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, VLevel.inst]
  change (fields ++ levels).getD (count + i) .zero = levels[i]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  simp only [Option.getD_some]
  rw [List.getElem_append_right (by omega)]
  simp only [hfields, Nat.add_sub_cancel_left]

private theorem restored_source_levels {r : Restoration} {e output : VExpr}
    (h : r.expr (e.instL generic) = some output) :
    ∃ original, r.expr e = some original ∧ output = original.instL generic := by
  have hh := r.expr_instL e generic
  rw [h] at hh
  cases he : r.expr e with
  | none => simp [he] at hh
  | some original => exact ⟨original, rfl, (Option.some.inj (by simpa [he] using hh)).symm⟩

/-- Restored source syntax depends only on the source-universe suffix of a
projection instance, including specialized auxiliary head parameters. -/
theorem restored_generic_levelEquiv {r : Restoration} {e output : VExpr}
    (h : r.expr (e.instL ((List.range n).map fun i => .param (count + i))) = some output)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = n) (hlevels' : levels'.length = n)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels') :
    LEquiv U (output.instL (fields ++ levels)) (output.instL (fields' ++ levels')) := by
  obtain ⟨original, _, rfl⟩ := restored_source_levels h
  simp only [VExpr.instL_instL, shifted_levels_inst hfields hlevels,
    shifted_levels_inst hfields' hlevels']
  exact LEquiv.instL_expr original hw hw' heq

private theorem restored_list_generic_levelEquiv {r : Restoration}
    (h : input.mapM (fun e => r.expr (e.instL
      ((List.range n).map fun i => .param (count + i)))) = some output)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = n) (hlevels' : levels'.length = n)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels') :
    ∀ e ∈ output, LEquiv U (e.instL (fields ++ levels)) (e.instL (fields' ++ levels')) := by
  have hh := List.mapM_eq_some.mp h
  clear h
  induction hh with
  | nil => simp
  | @cons e out es outs h _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact restored_generic_levelEquiv h hfields hfields' hlevels hlevels' hw hw' heq
    · exact ih x hx

/-- The source parts of a generic projection telescope are independent of all
reserved field-sort parameters. -/
theorem projectionData_generic_levelEquiv {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    (h : schema.projectionData owner
      ((List.range schema.signature.uvars).map fun i => .param (count + i)) = some data)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = schema.signature.uvars)
    (hlevels' : levels'.length = schema.signature.uvars)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels') :
    ∀ e ∈ data.params ++ data.indices ++ data.fields ++ [data.major],
      LEquiv U (e.instL (fields ++ levels)) (e.instL (fields' ++ levels')) := by
  unfold projectionData at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i ctor hctor
  dsimp only at h
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨params, hp, indices, hi, domains, hd, cindices, hci, major, hm, constructor, hc, h⟩ := h
  split at h <;> try contradiction
  cases h
  have hmajor : schema.restoration.expr
      ((VExpr.mkApps (.const schema.signature.families[owner].name
        (VLevel.params schema.signature.uvars))
        (vars params.length indices.length ++ vars indices.length 0)).instL
          ((List.range schema.signature.uvars).map fun i => .param (count + i))) = some major := by
    have hgeneric : (((List.range schema.signature.uvars).map fun i => VLevel.param (count + i))).length = schema.signature.uvars := by simp
    simpa only [instL_mkApps, instL, VLevel.inst_map_id hgeneric,
      List.map_append, vars, List.map_map, Function.comp_def, InductiveSignature.familyApp] using hm
  intro e he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with ((he | he) | he) | rfl
  · exact restored_list_generic_levelEquiv hp hfields hfields' hlevels hlevels' hw hw' heq e he
  · exact restored_list_generic_levelEquiv hi hfields hfields' hlevels hlevels' hw hw' heq e he
  · exact restored_list_generic_levelEquiv hd hfields hfields' hlevels hlevels' hw hw' heq e he
  · exact restored_generic_levelEquiv hmajor hfields hfields' hlevels hlevels' hw hw' heq

private theorem related_map {α : Type} {R : VExpr → VExpr → Prop}
    {f g : α → VExpr} {xs : List α} (h : ∀ x ∈ xs, R (f x) (g x)) :
    List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem instL_vars (n k : Nat) (levels : List VLevel) :
    (vars n k).map (·.instL levels) = vars n k := by
  simp [vars, List.map_map, Function.comp_def, instL]

private theorem ProjectionData.arguments_instL (data : ProjectionData) (levels : List VLevel) :
    data.arguments.map (·.instL levels) = data.arguments := by
  simp [ProjectionData.arguments, List.map_append, instL_vars, instL]

/-- Each actual generation step is congruent across instances with the same
source universes. Its chosen elimination universe is compared only at the
complete, motive-bearing case call. -/
theorem ProjectionData.step_generic_congr {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    (hlookup : env.eliminators block schema)
    (hdata : schema.projectionData owner
      ((List.range schema.signature.uvars).map fun i => .param (count + i)) = some data)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = schema.signature.uvars)
    (hlevels' : levels'.length = schema.signature.uvars)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels')
    (hd : domain ∈ data.fields)
    (hprevious : ∀ p ∈ previous,
      CaseLevelEquiv env U (p.value.instL (fields ++ levels))
        (p.value.instL (fields' ++ levels'))) :
    CaseLevelEquiv env U
      ((data.step block owner.val
        ((List.range schema.signature.uvars).map fun i => .param (count + i))
        domain target previous).value.instL (fields ++ levels))
      ((data.step block owner.val
        ((List.range schema.signature.uvars).map fun i => .param (count + i))
        domain target previous).value.instL (fields' ++ levels')) := by
  have hsource := projectionData_generic_levelEquiv hdata hfields hfields' hlevels hlevels' hw hw' heq
  have hparams := related_map (fun e (he : e ∈ data.params) =>
    CaseLevelEquiv.levels (env := env) (hsource e (by simp [he])))
  have hindices := related_map (fun e (he : e ∈ data.indices) =>
    CaseLevelEquiv.levels (env := env) (hsource e (by simp [he])))
  have hdomains := related_map (fun e (he : e ∈ data.fields) =>
    CaseLevelEquiv.levels (env := env) (hsource e (by simp [he])))
  have hmajor := CaseLevelEquiv.levels (env := env) (hsource data.major (by simp))
  have hfield : CaseLevelEquiv env U
      ((data.fieldTarget domain previous).instL (fields ++ levels))
      ((data.fieldTarget domain previous).instL (fields' ++ levels')) := by
    unfold ProjectionData.fieldTarget
    rw [instantiateParams_instL, instantiateParams_instL]
    apply CaseLevelEquiv.instantiateParams (.levels (hsource domain (by simp [hd])))
    simp only [List.map_append, instL_vars, List.map_map, Function.comp_def, instL_mkApps,
      ProjectionData.arguments_instL]
    exact VEnv.case_forall₂_append (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl _))
      (related_map (fun p hp => (hprevious p hp).mkApps
        (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl _))))
  have hmotive := CaseLevelEquiv.wrapLams (VEnv.case_forall₂_append hindices (.cons hmajor .nil)) hfield
  have hminor := CaseLevelEquiv.wrapLams hdomains (CaseLevelEquiv.refl
    (.bvar (data.fields.length - 1 - previous.length)))
  simp only [ProjectionData.step, instL_wrapLams, instL_mkApps, instL,
    List.map_append, List.map_cons, List.map_nil, instL_liftN,
    shifted_levels_inst hfields hlevels, shifted_levels_inst hfields' hlevels', instL_vars]
  apply CaseLevelEquiv.wrapLams
    (VEnv.case_forall₂_append (VEnv.case_forall₂_append hparams hindices) (.cons hmajor .nil))
  apply CaseLevelEquiv.caseApp hlookup heq
  · obtain ⟨hp, hi, hc⟩ := projectionData_counts hdata
    simp only [List.length_append, List.length_cons, List.length_nil,
      vars, List.length_map, List.length_reverse, List.length_range, VEnv.caseMajorArity, hp, hi, hc]
  · exact VEnv.case_forall₂_append
      (VEnv.case_forall₂_append
        (VEnv.case_forall₂_append (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl _))
          (.cons hmotive.liftN (.cons hminor.liftN .nil)))
        (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl _)))
      (.cons (.refl _) .nil)

private theorem ProjectionData.prefix_generic_congr {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    {domains : List VExpr} {targets : List VLevel} {previous result : List ProjectionFunction}
    (hlookup : env.eliminators block schema)
    (hdata : schema.projectionData owner
      ((List.range schema.signature.uvars).map fun i => .param (count + i)) = some data)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = schema.signature.uvars)
    (hlevels' : levels'.length = schema.signature.uvars)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels')
    (hd : ∀ domain ∈ domains, domain ∈ data.fields)
    (hprevious : ∀ p ∈ previous,
      CaseLevelEquiv env U (p.value.instL (fields ++ levels))
        (p.value.instL (fields' ++ levels')))
    (hout : data.prefix block owner.val
      ((List.range schema.signature.uvars).map fun i => .param (count + i))
      domains targets previous = some result) :
    ∀ p ∈ result, CaseLevelEquiv env U (p.value.instL (fields ++ levels))
      (p.value.instL (fields' ++ levels')) := by
  induction targets generalizing domains previous with
  | nil => simp only [ProjectionData.prefix] at hout; cases hout; exact hprevious
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      apply ih (fun d hd' => hd d (by simp [hd'])) ?_ hout
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hprevious p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact data.step_generic_congr hlookup hdata hfields hfields' hlevels hlevels' hw hw' heq
          (hd domain (by simp)) hprevious

/-- Every selected function of the fixed generic prefix is congruent for
arbitrary field-sort witnesses and equivalent source-universe instances.
Typed soundness then determines only those field sorts actually used by it. -/
theorem genericProjectionPrefix_congr {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {result : List ProjectionFunction}
    (hlookup : env.eliminators block schema)
    (hout : schema.genericProjectionPrefix block owner count = some result)
    (hfields : fields.length = count) (hfields' : fields'.length = count)
    (hlevels : levels.length = schema.signature.uvars)
    (hlevels' : levels'.length = schema.signature.uvars)
    (hw : ∀ u ∈ levels, u.WF U) (hw' : ∀ u ∈ levels', u.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels') :
    ∀ p ∈ result, CaseLevelEquiv env U (p.value.instL (fields ++ levels))
      (p.value.instL (fields' ++ levels')) := by
  unfold genericProjectionPrefix projectionPrefix at hout
  split at hout <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hout
  obtain ⟨data, hdata, hout⟩ := hout
  exact data.prefix_generic_congr hlookup hdata hfields hfields' hlevels hlevels' hw hw' heq
    (fun _ h => h) (by simp) hout

end Lean4Lean.InductiveSignature.CaseSchema
