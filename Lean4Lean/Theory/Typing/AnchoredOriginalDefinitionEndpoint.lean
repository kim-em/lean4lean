import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints

/-! Original definition endpoints retain their actual declaration stages.
Universe specialization is interpreted by header/environment induction; the
reified specialization is never passed off as a smaller local proof child. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure

/-- The actual stored body, specialized in the pre-equation header. -/
noncomputable def DefinitionDeclarationOrigin.instantiatedBody
    {value : VDefVal} {levels : List VLevel} {U : Nat} (origin : DefinitionDeclarationOrigin sourceEnv declarations value)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Derivation origin.stage.header U [] (value.value.instL levels) (value.value.instL levels)
      (value.type.instL levels) :=
  Classical.choice (Derivation.reify (origin.bodyInstance levelsWF))

/-- The original type-formation level is selected from the earlier base
formation, before even the mutual constant headers were installed. -/
noncomputable def DefinitionDeclarationOrigin.instantiatedTypeLevel
    {value : VDefVal} {levels : List VLevel} {U : Nat} (origin : DefinitionDeclarationOrigin sourceEnv declarations value)
    (levelsWF : ∀ level ∈ levels, level.WF U) : VLevel :=
  (origin.typeInstance levelsWF).choose

/-- The specialized assigned-type formation stays in its actual earlier
base environment. No ambient source-domain typing is synthesized. -/
noncomputable def DefinitionDeclarationOrigin.instantiatedType
    {value : VDefVal} {levels : List VLevel} {U : Nat} (origin : DefinitionDeclarationOrigin sourceEnv declarations value)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Derivation origin.base U [] (value.type.instL levels) (value.type.instL levels)
      (.sort (DefinitionDeclarationOrigin.instantiatedTypeLevel origin levelsWF)) :=
  Classical.choice (Derivation.reify (origin.typeInstance levelsWF).choose_spec)

end Lean4Lean.AnchoredSource.Adapted
