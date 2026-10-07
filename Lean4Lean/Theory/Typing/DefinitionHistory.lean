import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation

/-! The actual environment declaration history determines its ordinary
definition pattern table, including mutually recursive definitions. -/

namespace Lean4Lean

/-- Only transparent definitions contribute native delta equations. -/
def VDecl.definitionEntries : VDecl → List VDefVal
  | .def value => [value]
  | .mutualDef values => values
  | _ => []

/-- Declaration histories store their newest declaration first. -/
def VEnv.definitionRegistry : List VDecl → Name → Option VDefVal
  | [] => fun _ => none
  | declaration :: declarations =>
    VEnv.installDefinitions (VEnv.definitionRegistry declarations) declaration.definitionEntries

namespace VEnv
variable {env : VEnv}
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules from Lean4Lean.Theory.Typing.NativeConstructorRigidity

private theorem declaration_le (H : VDecl.WF env declaration extended) : env ≤ extended := by
  cases H with
  | «axiom» _ ha | «opaque» _ ha => exact VEnv.addConst_le ha
  | «def» _ ha => exact (VEnv.addConst_le ha).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ ha _ =>
    rw [addDefEqs_as_rules]
    exact (VEnv.addConsts_le ha).trans VEnv.addDefEqRules_le
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    exact ((((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)).trans
      (VEnv.addConst_le hc)).trans (VEnv.addConst_le hd)).trans VEnv.addDefEq_le
  | induct _ ha =>
    cases ha with
    | intro _ _ _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      exact (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
        (VEnv.addProjections_le.trans (VEnv.addConstVals_le hr))).trans VEnv.addDefEqRules_le

private theorem definitionRegistry_decl
    (H : VDecl.WF env declaration extended)
    (hold : ∀ name value, old name = some value → DefinitionRegistered env value ∧ value.name = name)
    (hlookup : installDefinitions old declaration.definitionEntries name = some value) :
    DefinitionRegistered extended value ∧ value.name = name := by
  have hm := declaration_le H
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_registered ha' hold hlookup
  | mutualDef _ ha _ => exact installDefinitions_registered ha hold hlookup
  | «axiom» | «opaque» | «example» | quot | induct =>
    have hh : old name = some value := hlookup
    exact ⟨(hold _ _ hh).1.mono hm, (hold _ _ hh).2⟩


private theorem definitionRegistry_decl_new
    (H : VDecl.WF env declaration extended)
    (hmem : value ∈ declaration.definitionEntries) :
    installDefinitions old declaration.definitionEntries value.name = some value := by
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_lookup ha' hmem
  | mutualDef _ ha _ => exact installDefinitions_lookup ha hmem
  | «axiom» | «opaque» | «example» | quot | induct => cases hmem

private theorem definitionRegistry_decl_preserves
    (H : VDecl.WF env declaration extended)
    (hregistered : DefinitionRegistered env value) (hold : old value.name = some value) :
    installDefinitions old declaration.definitionEntries value.name = some value := by
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_preserves ha' hregistered hold
  | mutualDef _ ha _ => exact installDefinitions_preserves ha hregistered hold
  | «axiom» | «opaque» | «example» | quot | induct => exact hold


/-- A bare native constant equation can only be a transparent definition;
inductive and quotient equations have a constructor application as major. -/
private theorem declaration_constEquation_origin
    (H : VDecl.WF env declaration extended) (hdf : extended.defeqs equation)
    (hhead : equation.lhs = VExpr.const name levels) :
    (∃ value ∈ declaration.definitionEntries, equation = value.toDefEq) ∨ env.defeqs equation := by
  cases H with
  | «axiom» _ ha | «opaque» _ ha =>
    exact .inr (by rwa [VEnv.addConst_defeqs ha] at hdf)
  | «example» => exact .inr hdf
  | «def» _ ha =>
    rcases hdf with rfl | hdf
    · exact .inl ⟨_, List.mem_singleton_self _, rfl⟩
    · exact .inr (by rwa [VEnv.addConst_defeqs ha] at hdf)
  | mutualDef _ ha _ =>
    rw [addDefEqs_as_rules, defeqs_addRules] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
      exact .inl ⟨value, hvalue, rfl⟩
    · have he := VEnv.addConstVals_defeqs (addConsts_as_values ▸ ha)
      exact .inr (by rwa [he] at hdf)
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    rcases hdf with rfl | hdf
    · cases hhead
    · exact .inr (by rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
        VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf)
  | induct _ ha =>
    cases ha with
    | intro _ hcompile _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      rw [defeqs_addRules] at hdf
      rcases hdf with hmem | hdf
      · obtain ⟨_, ⟨fn, us, args, hmajor⟩, _⟩ := hcompile.compiled.equation_major_origin equation hmem
        rw [hhead] at hmajor
        cases hmajor
      · exact .inr (by rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf)

/-- Every entry of the history-derived table is an actual installed
constant and defining equation at the indicated name. -/
theorem WF'.definitionRegistry_registered (H : env.WF' declarations)
    (hlookup : definitionRegistry declarations name = some value) :
    DefinitionRegistered env value ∧ value.name = name := by
  induction H generalizing name value with
  | empty => cases hlookup
  | decl hd _ ih =>
    exact definitionRegistry_decl hd (fun _ _ h => ih h) hlookup
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hr, hn⟩ := ih hlookup
    exact ⟨hr.mono VEnv.addProjections_le, hn⟩
  | inductEliminators _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hr, hn⟩ := ih hlookup
    exact ⟨hr.mono VEnv.addEliminator_le, hn⟩

/-- Every transparent definition in the actual history remains represented
by its exact value, even after later inductive and schema installation. -/
theorem WF'.definitionRegistry_complete (H : env.WF' declarations)
    (hdecl : declaration ∈ declarations) (hvalue : value ∈ declaration.definitionEntries) :
    definitionRegistry declarations value.name = some value := by
  induction H with
  | empty => cases hdecl
  | decl hd henv ih =>
    rcases List.mem_cons.mp hdecl with rfl | hdecl
    · exact definitionRegistry_decl_new hd hvalue
    · have hold := ih hdecl
      exact definitionRegistry_decl_preserves hd (henv.definitionRegistry_registered hold).1 hold
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hdecl
  | inductEliminators _ _ _ _ _ _ _ _ _ ih => exact ih hdecl

/-- The history itself produces each definition's concrete equation trace;
no caller supplies a reduction-coverage assertion. -/
theorem WF'.definition_equation_trace (H : env.WF' declarations)
    (hdecl : declaration ∈ declarations) (hvalue : value ∈ declaration.definitionEntries)
    (hlength : levels.length = value.uvars) :
    NativeReductionTrace env U (DefinitionPattern (definitionRegistry declarations)) Γ
      (value.toDefEq.lhs.instL levels) (value.toDefEq.rhs.instL levels) := by
  have hl := H.definitionRegistry_complete hdecl hvalue
  exact DefinitionPattern.equation_trace hl
    ((H.definitionRegistry_registered hl).1.closed ⟨declarations, H⟩) hlength

/-- Every actual bare-constant equation is represented by the exact value
in the extracted table. Other equation kinds are excluded by generation. -/
theorem WF'.definitionRegistry_of_constantEquation (H : env.WF' declarations)
    (hdf : env.defeqs equation) (hhead : equation.lhs = VExpr.const name levels) :
    ∃ value, definitionRegistry declarations name = some value ∧ equation = value.toDefEq := by
  induction H generalizing name levels with
  | empty => cases hdf
  | decl hd henv ih =>
    rcases declaration_constEquation_origin hd hdf hhead with ⟨value, hmem, rfl⟩ | hold
    · have hn : value.name = name := (VExpr.const.inj hhead).1
      rw [← hn]
      exact ⟨value, definitionRegistry_decl_new hd hmem, rfl⟩
    · obtain ⟨value, hlookup, heq⟩ := ih hold hhead
      have hr := henv.definitionRegistry_registered hlookup
      rw [← hr.2] at hlookup ⊢
      exact ⟨value, definitionRegistry_decl_preserves hd hr.1 hlookup, heq⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih (by simpa only [VEnv.addProjections_defeqs] using hdf) hhead
  | inductEliminators _ _ _ _ _ _ _ _ _ ih =>
    exact ih hdf hhead

/-- Bare-constant equation coverage is therefore produced for every
actual stored equation of that shape, not merely a chosen declaration. -/
theorem WF'.constantEquation_trace (H : env.WF' declarations)
    (hdf : env.defeqs equation) (hhead : equation.lhs = VExpr.const name sourceLevels)
    (hlength : levels.length = equation.uvars) :
    NativeReductionTrace env U (DefinitionPattern (definitionRegistry declarations)) Γ
      (equation.lhs.instL levels) (equation.rhs.instL levels) := by
  obtain ⟨value, hl, rfl⟩ := H.definitionRegistry_of_constantEquation hdf hhead
  have hr := H.definitionRegistry_registered hl
  rw [← hr.2] at hl
  exact DefinitionPattern.equation_trace hl
    ((H.definitionRegistry_registered hl).1.closed ⟨declarations, H⟩) hlength

end VEnv
end Lean4Lean
