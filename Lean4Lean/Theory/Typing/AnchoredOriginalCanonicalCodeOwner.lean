import Lean4Lean.Theory.Typing.EquationControls

/-! A named code charge refers to one actual registered equation and the
original source selected by its equation stratification. This data is below
the shared query grammar; it contains no interpretation or recursive answer. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VEnv
set_option Elab.async false

structure CanonicalCodeOwner (env : VEnv) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (name : Name) where
  rule : VDefEq
  present : env.defeqs rule
  head : EquationStratification.headEquation registry name = some rule

namespace CanonicalCodeOwner
variable {env : VEnv} {registry : CanonicalHead.Registry}
  {strata : EquationStratification env} {name : Name}

noncomputable def selected (owner : CanonicalCodeOwner env registry strata name) :
    strata.Selected owner.rule := strata.select owner.present

theorem headOrdinal_eq (owner : CanonicalCodeOwner env registry strata name) :
    strata.headOrdinal registry name = owner.selected.ordinal := by
  simp only [EquationStratification.headOrdinal, owner.head,
    strata.ordinalOf_present owner.present, selected]

theorem sourceCutoff (owner : CanonicalCodeOwner env registry strata name) :
    strata.SourceCutoff owner.selected.origin.source (owner.selected.ordinal - 1) :=
  owner.selected.sourceCutoff

def ofDefinition (strata : EquationStratification env)
    (lookup : registry.definitions name = some value) (present : env.defeqs value.toDefEq) :
    CanonicalCodeOwner env registry strata name :=
  ⟨value.toDefEq, present, by simp only [EquationStratification.headEquation, lookup]⟩

end CanonicalCodeOwner
end Lean4Lean.AnchoredSource.Adapted
