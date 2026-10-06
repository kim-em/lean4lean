import Lean4Lean.Theory.Typing.Env

/-!
# Compatibility of eliminator schemas with registered structures

`VEnv.WF'.inductEliminators` does not compare a schema with the structures registered by
`inductProjections` over the same constants. Without a compatibility condition a schema can add
constructors to a registered structure, and the environment is inconsistent: register
`structure Unit : Type` with constructor `Unit.mk`, add an axiom `other : Unit`, and register a
schema (compiled in the empty base) for `inductive Unit : Type | mk | other`. Then
`elim C a b Unit.mk ≡ a` and `elim C a b other ≡ b` (generic equations), while `unitLike` gives
`Unit.mk ≡ other`; with `C := fun _ => Type`, `a := Prop`, `b := Prop → Prop` this derives
`Prop ≡ (Prop → Prop)`.

`SchemaStructCompat env`: for every registered schema and every registered structure `s` that is
an original family of the schema (at source slot `owner`), the schema's constructors of that slot
are exactly the structure's constructor.
-/

namespace Lean4Lean

/-- Every registered structure that is an original family of a registered schema has, in the
schema, exactly its registered constructor. -/
def SchemaStructCompat (env : VEnv) : Prop :=
  ∀ {key : Name} {schema : InductiveSignature.CaseSchema} {s : Name} {info : VProjectionInfo},
    env.eliminators key schema → env.projections s info →
    ∀ owner : Fin schema.signature.families.size,
      schema.originalFamilies[owner.val]? = some s →
      (schema.view owner).constructors.toList.map (·.name) = [info.ctorName]

/-- STUB (to be replaced by the specification fix of `VEnv.WF'.inductEliminators`, which adds
this compatibility as a premise): every well-formed history satisfies `SchemaStructCompat`. -/
theorem VEnv.WF'.schemaStructCompat {ds : List VDecl} {env : VEnv} (_H : env.WF' ds) :
    SchemaStructCompat env := by
  sorry

theorem VEnv.WF.schemaStructCompat {env : VEnv} (H : env.WF) : SchemaStructCompat env :=
  VEnv.WF'.schemaStructCompat H.choose_spec

end Lean4Lean
