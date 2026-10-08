import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.HeadInjectivity.Fields
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Separation

/-! # Head inversion for types: the base obligation of the inversion layer

The statements (`HeadInversion`, `HeadSeparation`, `HeadInjectivity`) and the chain lemmas are in
`HeadInversionDefs.lean`. Both halves are proved for every well-formed environment from the glued
observation model (`Theory/Typing/HeadInjectivity/Model/`): separation by
`VEnv.WF.headSeparationModel`, injectivity by `VEnv.WF.headInjectivityCore`.

This file and the model do not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
`FullReduction` or `HeadReduction`: `VEnv.WF.headInversion`, assembled here, is the single
semantic fact from which uniqueness of types (`IsDefEq.uniq`) and every inversion lemma in
`Injectivity.lean` are derived.

See `docs/inductives/history/BASE_OBLIGATIONS_DESIGN.md`, section 4, Phase 0. -/

namespace Lean4Lean
namespace VEnv

/-- Separation for every well-formed environment, from the glued observation model. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparation {env : VEnv} (henv : env.WF) :
    env.HeadSeparation :=
  henv.headSeparationModel

/-- Injectivity of type heads for every well-formed environment: the chain-level core from
soundness of the glued observation model (`VEnv.WF.headInjectivityCore`,
`Theory/Typing/HeadInjectivity/Model/EnvValid.lean`), lifted by the syntactic layer
(`VEnv.HeadInjectivityCore.toHeadInjectivity`). -/
theorem _root_.Lean4Lean.VEnv.WF.headInjectivity {env : VEnv} (henv : env.WF) :
    env.HeadInjectivity :=
  henv.headInjectivityCore.toHeadInjectivity henv

/-- The base obligation of the inversion layer, assembled from separation and injectivity.

It replaces the five former Injectivity conjectures (`IsDefEqU.sort_inv`,
`forallE_inv_stratified`, `sort_forallE_inv`, `fieldType_inv_stratified`, `rigidApp_inv`)
and the missing head separations (rigid head against Pi, sort against rigid head, distinct
rigid heads). Uniqueness of types (`IsDefEq.uniq`), all inversion lemmas in
`Injectivity.lean`, and `VConstructorShape.saturated_of_hasType` are derived from it. -/
theorem _root_.Lean4Lean.VEnv.WF.headInversion {env : VEnv} (henv : env.WF) :
    env.HeadInversion :=
  have hs := henv.headSeparation
  have hi := henv.headInjectivity
  { sort_sort := hs.sort_sort
    forallE_forallE := hi.forallE_forallE
    rigid_rigid := fun hΓ hc hc' H =>
      have ⟨h1, h2⟩ := hs.rigid_heads hΓ hc hc' H
      ⟨h1, h2, by subst h1; exact hi.rigid_args hΓ hc H⟩
    former_args := hi.former_args
    sort_forallE := hs.sort_forallE
    sort_rigid := hs.sort_rigid
    forallE_rigid := hs.forallE_rigid
    proj_fieldType := hi.proj_fieldType }

end VEnv
end Lean4Lean
