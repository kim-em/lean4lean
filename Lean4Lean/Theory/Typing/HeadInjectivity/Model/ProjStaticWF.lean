import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid
import Lean4Lean.Theory.Typing.ShapeModel.EnvSigOrigin

/-! # Static facts about projection entries of well-formed environments

The constructor and family tables of the shape model (`ShapeModel.ctorOf`, `ShapeModel.famOf`,
`Theory/Typing/ShapeModel/EnvTables.lean`) record every registered structure with its
constructor, every native constructor major, and every generic case major of a registered
schema whose view is the recorded one. A family is never a constructor of the tables, and table
entries are rigid. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

variable {env : VEnv}

/-- The major of a generic case rule of a registered schema is literally its constructor. -/
theorem Model.generates_major {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {rule : CaseSchema.AppliedRule} (hgen : schema.Generates key owner rule) :
    ∃ fn ls args, rule.equation.lhs.stripLams =
      .app fn (VExpr.mkApps (.const rule.application.ctorName ls) args) := by
  obtain ⟨_, _, _, hextract⟩ := hgen
  have hb := (CaseSchema.Generates.body_exact ⟨_, ‹_›, ‹_›, hextract⟩).1
  have ha := CaseSchema.Application.extract_sound
    (CaseSchema.AppliedRule.extract_spec hextract).2.2.1
  refine ⟨VExpr.mkApps (.elim rule.application.block rule.application.owner
    rule.application.levels) rule.application.arguments, rule.application.ctorLevels,
    rule.application.ctorArguments, ?_⟩
  rw [← hb, ShapeModel.stripLams_wrapLams', ← ha]
  rfl

/-- A native constructor is a constructor of the table. -/
theorem WF.ctorOf_of_nativeCtor (henv : env.WF) (h : Model.IsNativeCtor env c) :
    ShapeModel.ctorOf env c ≠ none := by
  obtain ⟨df, hdf, fn, ls, args, hm⟩ := h
  obtain ⟨k, _, _, hk, _⟩ := ShapeModel.defeq_major henv hdf hm
  simp [hk]

/-- A case constructor is a constructor of the table, or a constructor, in the schema's view, of
an original family of the schema which is its syntactic family. -/
theorem WF.caseCtor_origin (henv : env.WF) (h : Model.IsCaseCtor env c) :
    ShapeModel.ctorOf env c ≠ none ∨ ∃ (key : Name) (schema : CaseSchema)
      (owner : Fin schema.signature.families.size), env.eliminators key schema ∧
      schema.originalFamilies[owner.val]? = ShapeModel.ctorFamily env c ∧
      c ∈ (schema.view owner).constructors.toList.map (·.name) := by
  obtain ⟨key, schema, owner, rule, hreg, hgen, rfl⟩ := h
  obtain ⟨fn, ls, args, hm⟩ := Model.generates_major hgen
  obtain ⟨rules, hrules, hmem, -⟩ := hgen
  rcases ShapeModel.generic_major_origin henv hreg hrules hmem hm with h | ⟨ho, hc⟩
  · exact .inl h
  · exact .inr ⟨key, schema, owner, hreg, ho, hc⟩

theorem Model.ctorFamily_of_ctorFam (h : Model.CtorFam env c I) :
    ShapeModel.ctorFamily env c = some I := by
  obtain ⟨ci, ls, hci, hres⟩ := h
  simp [ShapeModel.ctorFamily, hci, ShapeModel.familyOfType, hres]

/-- **The constructor of a registered structure is rigid.** -/
theorem WF.projCtor_rigid (henv : env.WF) : Model.IsProjCtor env c → env.Rigid c := by
  rintro ⟨fam, info, hp, rfl⟩
  exact (ShapeModel.ctorOf_rigid henv (ShapeModel.ctorOf_projection henv hp)).1

/-- A registered structure is not the constructor of a registered structure. -/
theorem WF.projFamily_not_projCtor (henv : env.WF) (hp : env.projections S info) :
    ¬ Model.IsProjCtor env S := by
  rintro ⟨fam, info', hp', hn⟩
  have h1 := (ShapeModel.ctorOf_rigid henv (ShapeModel.ctorOf_projection henv hp)).2.2
  rw [← hn, ShapeModel.ctorOf_projection henv hp'] at h1
  cases h1

/-- A registered structure is not a native constructor. -/
theorem WF.projFamily_not_nativeCtor (henv : env.WF) (hp : env.projections S info) :
    ¬ Model.IsNativeCtor env S := fun h => henv.ctorOf_of_nativeCtor h
  (ShapeModel.ctorOf_rigid henv (ShapeModel.ctorOf_projection henv hp)).2.2

/-- **The only way a registered structure `S` can be a case constructor**: some registered
schema lists `S` among the constructors, in its own view, of a slot whose original family is the
family `ShapeModel.ctorFamily env S` that the declared type of `S` literally returns. This cannot
happen in a consistent environment (the declared type of `S` is definitionally a telescope ending
in a sort), but excluding it needs head inversion for earlier environments, not only the
declaration history: the schema may be registered after the structure, and its certification
base need not contain `S`. -/
theorem WF.projFamily_caseCtor (henv : env.WF) (hp : env.projections S info)
    (h : Model.IsCaseCtor env S) :
    ∃ (key : Name) (schema : CaseSchema) (owner : Fin schema.signature.families.size),
      env.eliminators key schema ∧
      schema.originalFamilies[owner.val]? = ShapeModel.ctorFamily env S ∧
      S ∈ (schema.view owner).constructors.toList.map (·.name) := by
  rcases henv.caseCtor_origin h with h | h
  · exact absurd (ShapeModel.ctorOf_rigid henv (ShapeModel.ctorOf_projection henv hp)).2.2 h
  · exact h

/-- **Static facts of a projection entry** (`Model.ProjStatic`) of a well-formed environment,
given that its family is not a case constructor (`WF.projFamily_caseCtor` describes the only
remaining corner). -/
theorem WF.projStatic (henv : env.WF) (hp : env.projections S info)
    (hcase : ¬ Model.IsCaseCtor env S) : Model.ProjStatic env S info := by
  have hk := ShapeModel.ctorOf_projection henv hp
  have hr := ShapeModel.ctorOf_rigid henv hk
  refine ⟨hr.2.1, hr.1, ?_, henv.projFamily_not_projCtor hp, ?_⟩
  · rintro (h | h)
    · exact henv.projFamily_not_nativeCtor hp h
    · exact hcase h
  · exact henv.ordered.closedC (henv.ordered.projectionConstructor hp)

/-- **A constructor of a registered structure belongs to that structure.** -/
theorem WF.projCtor_family (henv : env.WF) (hpc : Model.IsProjCtor env c)
    (hcf : Model.CtorFam env c I) : ∃ info, env.projections I info ∧ info.ctorName = c := by
  obtain ⟨fam, info, hp, rfl⟩ := hpc
  have h1 := (ShapeModel.ctorOf_shape' henv (ShapeModel.ctorOf_projection henv hp)).family
  rw [Model.ctorFamily_of_ctorFam hcf] at h1
  cases h1
  exact ⟨info, hp, rfl⟩

/-- **A registered structure has exactly its registered constructor** among the constructors
(native or case) whose type returns it. -/
theorem WF.ctor_of_projFamily (henv : env.WF) (hp : env.projections I info)
    (hc : Model.IsCtor env c) (hcf : Model.CtorFam env c I) : c = info.ctorName := by
  have hf := Model.ctorFamily_of_ctorFam hcf
  have fromTable : ShapeModel.ctorOf env c ≠ none → c = info.ctorName := by
    intro h
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    have hfam := (ShapeModel.ctorOf_shape' henv hk).family
    rw [hf] at hfam
    cases hfam
    have hmem := (ShapeModel.famOf_mem_ctors henv (ShapeModel.famOf_projection henv hp)).mpr
      ⟨k, hk, rfl⟩
    simpa using hmem
  rcases hc with h | h
  · exact fromTable (henv.ctorOf_of_nativeCtor h)
  · rcases henv.caseCtor_origin h with h | ⟨key, schema, owner, hreg, ho, hmem⟩
    · exact fromTable h
    · rw [hf] at ho
      rw [henv.schemaStructCompat hreg hp owner ho] at hmem
      simpa using hmem

end VEnv
end Lean4Lean
