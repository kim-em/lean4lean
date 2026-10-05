import Lean4Lean.Theory.Inductive.CaseRegistration

/-! The abstract eliminator header is determined by a fresh registration.
This metadata invariant is weaker than full environment well-formedness and
is not implied by `Ordered`, whose eliminator constructor permits repeats. -/
namespace Lean4Lean.VEnv
open InductiveSignature

/-- One schema per abstract block key. -/
def EliminatorsUnique (env : VEnv) : Prop :=
  ∀ {key left right}, env.eliminators key left → env.eliminators key right → left = right

theorem WF.eliminatorsUnique {env : VEnv} (formed : env.WF) : env.EliminatorsUnique :=
  fun left right => formed.eliminators_unique left right

theorem EliminatorsUnique.restrict {env source : VEnv} (unique : env.EliminatorsUnique) (below : source ≤ env) :
    source.EliminatorsUnique :=
  fun left right => unique (below.eliminators left) (below.eliminators right)

theorem EliminatorsUnique.of_registry_eq {env base : VEnv} (unique : base.EliminatorsUnique)
    (same : env.eliminators = base.eliminators) : env.EliminatorsUnique := by
  unfold EliminatorsUnique
  rw [same]
  exact unique

theorem EliminatorsUnique.register {env : VEnv} (unique : env.EliminatorsUnique)
    (fresh : ∀ previous, ¬ env.eliminators key previous) :
    (env.addEliminator key schema).EliminatorsUnique := by
  intro block left right leftRegistered rightRegistered
  rcases leftRegistered with ⟨rfl, rfl⟩ | leftRegistered
  · rcases rightRegistered with ⟨_, rfl⟩ | rightRegistered
    · rfl
    · exact (fresh _ rightRegistered).elim
  · rcases rightRegistered with ⟨rfl, rfl⟩ | rightRegistered
    · exact (fresh _ leftRegistered).elim
    · exact unique leftRegistered rightRegistered

/-- The actual constructor boundary preserves the old registry and adds a
fresh declaration-derived schema. No current recursor equation is used. -/
theorem eliminatorsUnique_after_constructors
    {schema : CaseSchema} {base envTypes envCtors : VEnv}
    (certified : schema.Certified base source block) (baseFormed : base.WF)
    (keySelected : source.types.head?.map (·.name) = some key)
    (types : base.addConstVals block.types = some envTypes)
    (constructors : envTypes.addConstVals block.ctors = some envCtors)
    (entries : List VProjectionEntry) :
    ((envCtors.addProjections entries).addEliminator key schema).EliminatorsUnique := by
  have unchanged : (envCtors.addProjections entries).eliminators = base.eliminators := by
    rw [VEnv.addProjections_eliminators, VEnv.addConstVals_eliminators constructors,
      VEnv.addConstVals_eliminators types]
  have unique : (envCtors.addProjections entries).EliminatorsUnique :=
    EliminatorsUnique.of_registry_eq baseFormed.eliminatorsUnique unchanged
  have fresh := (certified.fresh baseFormed keySelected).of_registry_eq unchanged
  intro registeredKey left right leftRegistered rightRegistered
  exact EliminatorsUnique.register (schema := schema) unique fresh.1 leftRegistered rightRegistered

end Lean4Lean.VEnv
