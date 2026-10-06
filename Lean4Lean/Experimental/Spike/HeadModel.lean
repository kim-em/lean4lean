import Lean4Lean.Theory.Typing.HeadSeparationModel

/-! # Phase 1 spike: the separation half of `HeadInversion` from a sound model

`VEnv.HeadInversion` mixes two kinds of statement.

* *Separation*: `sort_sort` (levels of equal sorts are `≈`), `sort_forallE`, `sort_rigid`,
  `forallE_rigid`, and the head/level part of `rigid_rigid` (`c = c'` and `ls ≈ ls'`).
  These only say that a chain cannot connect two types with different *head classes*.
* *Injectivity*: `forallE_forallE`, the argument part of `rigid_rigid`, `former_args` and
  `proj_fieldType`. These produce *declarative* derivations between components.

This file shows that the separation half needs no logical relation and no adequacy
theorem: it follows from any compositional model that is sound for `IsDefEq` and assigns
the expected head class to sorts, Pi types and saturated rigid applications. The model is
an interface (`HeadModel`, now in `Theory/Typing/HeadSeparationModel.lean`); nothing here
constructs one. A shape model in the style of
`Experimental/ShapeLogRel.lean`, with sort shapes carrying the evaluated level and inductive
type shapes carrying the family name and evaluated levels, is the intended instance (see
`Spike/README.md`, section "Separation from soundness alone").

The injectivity half is where the semantic route meets the obstruction recorded in
`Spike/ReadThrough.lean`.

No `sorry` and no axioms. -/

namespace Lean4Lean
namespace Spike
open VEnv

/-! The interface `HeadClass`, `HeadModel`, `HeadModel.separation` (and
`HeadModel.Compositional`) now lives in `Theory/Typing/HeadSeparationModel.lean`, where the shape
model instantiates it (`ShapeModel.headModel_of_shapeModel`). -/

/-- The separation half is exactly the corresponding part of `HeadInversion`. -/
theorem HeadInversion.toHeadSeparation {env : VEnv} (h : env.HeadInversion) :
    HeadSeparation env where
  sort_sort := h.sort_sort
  sort_forallE := h.sort_forallE
  sort_rigid := h.sort_rigid
  forallE_rigid := h.forallE_rigid
  rigid_heads hΓ hc hc' H := let ⟨h1, h2, _⟩ := h.rigid_rigid hΓ hc hc' H; ⟨h1, h2⟩

end Spike
end Lean4Lean
