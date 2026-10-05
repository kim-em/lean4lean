import Lean4Lean.Theory.Typing.AnchoredConversion
import Lean4Lean.Theory.Typing.AnchoredTransitivity

/-! Concrete anchor operations used by source application and hereditary
observation views. Supports are selected from the actual admission witnesses;
neither operation asks for a new source observation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {key : Key n} {anchor left right : VExpr}

/-- An admitted argument realizes the same input demand when frozen as its
own anchor. Its existing self-evidence supplies both semantic clauses. -/
theorem Admitted.reset_anchor
    (h : Admitted env U registry Γ key anchor anchor) :
    Admitted env U registry Γ { key with anchor := anchor } anchor anchor := by
  obtain ⟨_, pair, support, typed, formation, code, _, self⟩ := h
  exact ⟨pair, pair, support, typed, formation, code, self, self⟩

/-- A row accepting a new anchor accepts all arguments admitted by that
newly anchored row. This is the direction required when reusing its behavior. -/
theorem Admitted.prepend_anchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (seed : Admitted env U registry Γ key anchor anchor)
    (h : Admitted env U registry Γ { key with anchor := anchor } left right) :
    Admitted env U registry Γ key left right := by
  obtain ⟨rawSeed, _, oldSupport, _, _, _, first, _⟩ := seed
  obtain ⟨rawAnchor, rawPair, support, typed, formation, code, next, pair⟩ := h
  exact ⟨rawSeed.trans rawAnchor, rawPair, support, typed, formation, code,
    Related.trans henv hscoped first next, pair⟩

end Lean4Lean.AnchoredSemantics
