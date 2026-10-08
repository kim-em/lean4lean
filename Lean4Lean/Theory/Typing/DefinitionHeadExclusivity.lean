import Lean4Lean.Theory.Typing.DefinitionHistory

/-! Definition heads are exclusive in the actual declaration history.
Later inductive or quotient equations cannot acquire an occupied head. -/

namespace Lean4Lean.VEnv
variable {env : VEnv}
open private declaration_le definitionRegistry_decl_new
  from Lean4Lean.Theory.Typing.DefinitionHistory
open private addConsts_as_values addDefEqs_as_rules defeqs_addRules addConst_fresh
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

private theorem declaration_old_equation
    (H : VDecl.WF env declaration extended)
    (hoccupied : env.constants name = some constant) (hdf : extended.defeqs equation)
    (hhead : equation.lhs.nativeEquationHead = VExpr.const name levels) :
    env.defeqs equation := by
  have exclude {later : VEnv} (hle : env ≤ later) (hf : later.constants name = none) : False := by
    have hs := hle.constants hoccupied
    rw [hf] at hs
    contradiction
  cases H with
  | «axiom» _ ha | «opaque» _ ha => rwa [VEnv.addConst_defeqs ha] at hdf
  | «example» => exact hdf
  | «def» _ ha =>
    rcases hdf with rfl | hdf
    · have hn := (VExpr.const.inj hhead).1
      have hf := addConst_fresh ha
      rw [hn] at hf
      exact (exclude .rfl hf).elim
    · rwa [VEnv.addConst_defeqs ha] at hdf
  | mutualDef _ ha _ =>
    rw [addDefEqs_as_rules, defeqs_addRules] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
      have hn := (VExpr.const.inj hhead).1
      have hf := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ ha)
        value.toVConstVal (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
      change env.constants value.name = none at hf
      rw [hn] at hf
      exact (exclude .rfl hf).elim
    · rwa [VEnv.addConstVals_defeqs (addConsts_as_values ▸ ha)] at hdf
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    rcases hdf with rfl | hdf
    · have hn : ``Quot.lift = name := (VExpr.const.inj hhead).1
      have hf := addConst_fresh hc
      rw [hn] at hf
      exact (exclude ((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)) hf).elim
    · rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
        VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf
  | induct _ ha =>
    cases ha with
    | intro _ hcompile _ _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      rw [defeqs_addRules] at hdf
      rcases hdf with hmem | hdf
      · obtain ⟨rec, hrec, us, howned⟩ := hcompile.compiled.equation_head_owned equation hmem
        rw [VExpr.nativeEquationHead_eq] at hhead
        have hn := (VExpr.const.inj (howned.symm.trans hhead)).1
        have hf := VEnv.addConstVals_names_fresh hr rec hrec
        rw [hn] at hf
        exact (exclude (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
          VEnv.addEliminators_addProjections_le) hf).elim
      · rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf

private theorem declaration_new_definition_head
    (hordered : env.Ordered) (H : VDecl.WF env declaration extended)
    (hvalue : value ∈ declaration.definitionEntries) (hdf : extended.defeqs equation)
    (hhead : equation.lhs.nativeEquationHead = VExpr.const value.name levels) :
    equation = value.toDefEq := by
  have exclude (hfresh : env.constants value.name = none) (hdf : env.defeqs equation) : False := by
    exact hordered.rigid_of_absent hfresh equation hdf levels
      ((VExpr.nativeEquationHead_eq _).symm.trans hhead)
  cases H with
  | «axiom» | «opaque» | «example» | quot | induct => cases hvalue
  | «def» hw ha =>
    have hv : value = _ := List.mem_singleton.mp hvalue
    subst value
    rcases hdf with rfl | hdf
    · rfl
    · have hh : env.defeqs equation := by rwa [VEnv.addConst_defeqs ha] at hdf
      exact (exclude (addConst_fresh ha) hh).elim
  | mutualDef htypes ha hvalues =>
    rename_i values next
    rw [addDefEqs_as_rules, defeqs_addRules] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨other, hother, rfl⟩ := List.mem_map.mp hmem
      have hn : other.name = value.name := (VExpr.const.inj hhead).1
      have hleft := installDefinitions_lookup (old := fun _ => none) ha hother
      have hright := installDefinitions_lookup (old := fun _ => none) ha hvalue
      rw [hn] at hleft
      cases Option.some.inj (hleft.symm.trans hright)
      rfl
    · have hf := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ ha)
        value.toVConstVal (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
      have hh : env.defeqs equation := by
        rwa [VEnv.addConstVals_defeqs (addConsts_as_values ▸ ha)] at hdf
      exact (exclude hf hh).elim

/-- All equations at an ordinary definition's computational head are its
one exact defining equation. This excludes definition/native-iota overlap. -/
theorem WF'.definition_head_exclusive (H : env.WF' declarations)
    (hlookup : definitionRegistry declarations name = some value)
    (hdf : env.defeqs equation)
    (hhead : equation.lhs.nativeEquationHead = VExpr.const name levels) :
    equation = value.toDefEq := by
  induction H generalizing name value with
  | empty => cases hdf
  | decl hd henv ih =>
    rename_i declaration next ds previous
    change installDefinitions _ _ _ = some value at hlookup
    unfold installDefinitions at hlookup
    cases hf : declaration.definitionEntries.find? (fun value => value.name == name) with
    | none =>
      have hold : definitionRegistry ds name = some value := by simpa [hf] using hlookup
      have hr := henv.definitionRegistry_registered hold
      have heq := declaration_old_equation hd (hr.2 ▸ hr.1.1) hdf hhead
      exact ih hold heq hhead
    | some found =>
      simp only [hf, Option.orElse_some, Option.some.injEq] at hlookup
      subst found
      have hn : value.name = name := by simpa using List.find?_some hf
      exact declaration_new_definition_head (VEnv.WF.ordered ⟨_, henv⟩) hd
        (List.mem_of_find?_eq_some hf) hdf (hn ▸ hhead)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih hlookup (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using hdf) hhead
  | inductEliminators _ _ _ _ _ _ _ _ _ ih => exact ih hlookup hdf hhead

/-- The public registration witness inherits head exclusivity from the
actual well-formed environment history. -/
theorem DefinitionRegistered.head_exclusive (henv : env.WF)
    (H : DefinitionRegistered env value) (hdf : env.defeqs equation)
    (hhead : equation.lhs.nativeEquationHead = VExpr.const value.name levels) :
    equation = value.toDefEq := by
  obtain ⟨declarations, hwf⟩ := henv
  obtain ⟨stored, hl, he⟩ := hwf.definitionRegistry_of_constantEquation H.2 rfl
  exact (hwf.definition_head_exclusive hl hdf hhead).trans he.symm

/-- A real constructor-major equation cannot overlap a transparent
definition at its computational head. -/
theorem DefinitionRegistered.not_constructor_equation (henv : env.WF)
    (H : DefinitionRegistered env value) (hdf : env.defeqs equation)
    (hhead : equation.lhs.nativeEquationHead = VExpr.const value.name levels)
    (hmajor : equation.HasConstructorMajor ctorName) : False := by
  rw [H.head_exclusive henv hdf hhead] at hmajor
  obtain ⟨fn, levels, args, he⟩ := hmajor
  cases he

end Lean4Lean.VEnv
