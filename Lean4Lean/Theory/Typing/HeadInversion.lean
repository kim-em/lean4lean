import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.HeadInjectivity.Fields

/-! # Head inversion for types: the base obligation of the inversion layer

The statements (`HeadInversion`, `HeadSeparation`, `HeadInjectivity`) and the chain lemmas are in
`HeadInversionDefs.lean`. Both halves are proved for every well-formed environment from the glued
observation model (`Theory/Typing/HeadInjectivity/Model/`, on the verified-inductives branch):
separation by `VEnv.WF.headSeparationModel`, injectivity by `VEnv.WF.chainHeadInjectivity`.

**Wave 0 of the port onto the ι pattern calculus**: the model is not yet ported, so its two
theorems are stated here as stubs (`sorry`, marked `WAVE 0 STUB`), to be proved in wave 1C by
porting the model with a `pat` clause in its rule soundness (`Model/RuleSound.lean`). Every
inversion lemma of `Injectivity.lean` and uniqueness of types (`IsDefEq.uniq`) are derived
from these two statements through the syntactic layer (`HeadInjectivity/{ChainInjectivity,
Congruence, FieldType, Uniqueness, Fields}.lean`), which is ported and proved.

This file and the model do not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
`FullReduction` or `HeadReduction` (section 4.1 of the design notes). -/

namespace Lean4Lean
namespace VEnv

/-- Chain-level head injectivity for every well-formed environment, from soundness of the
glued observation model (`HeadInjectivity/Model/EnvValid.lean` on the source branch).

WAVE 0 STUB: the model is ported in wave 1C, with a `pat` clause for the registered ι rules
(`env.pats`) in place of the stored-equation clause. -/
theorem _root_.Lean4Lean.VEnv.WF.chainHeadInjectivity {env : VEnv} (henv : env.WF) :
    env.ChainHeadInjectivity := by
  -- WAVE 0 STUB
  sorry

/-- Separation for every well-formed environment, from the glued observation model
(`HeadInjectivity/Model/Separation.lean` on the source branch): a sort has a `sort`
observation, a Pi type a `piDom` observation, a rigid spine neither.

WAVE 0 STUB: the model is ported in wave 1C. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparationModel {env : VEnv} (henv : env.WF) :
    env.HeadSeparation := by
  -- WAVE 0 STUB
  sorry

/-- Separation for every well-formed environment, from the glued observation model. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparation {env : VEnv} (henv : env.WF) :
    env.HeadSeparation :=
  henv.headSeparationModel

/-- Injectivity of type heads for every well-formed environment: the chain-level core from
soundness of the glued observation model (`VEnv.WF.chainHeadInjectivity`), lifted by the
syntactic layer (`VEnv.ChainHeadInjectivity.toHeadInjectivity`). -/
theorem _root_.Lean4Lean.VEnv.WF.headInjectivity {env : VEnv} (henv : env.WF) :
    env.HeadInjectivity :=
  henv.chainHeadInjectivity.toHeadInjectivity henv

/-- The base obligation of the inversion layer, assembled from separation and injectivity.

All inversion lemmas in `Injectivity.lean` are derived from it; uniqueness of types
(`IsDefEq.uniq`) uses the chain-level core directly. -/
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
