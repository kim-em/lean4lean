import Lean4Lean.Theory.Typing.AnchoredSymmetry
import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredViewMaps

/-! The reverse guard for a change of anchor uses the same actual support;
no source observation or replacement type cover is requested. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

/-- If a row admits a replacement anchor, the replaced row admits its old
anchor. The value demand and raw domain are unchanged. -/
theorem Admitted.reanchor_reverse
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {anchor : VExpr}
    (henv : env.Ordered)
    (H : Admitted env U registry Γ key anchor anchor) :
    Admitted env U registry Γ (reanchorKey key anchor) key.anchor key.anchor := by
  obtain ⟨raw, _, support, typed, formation, code, bridge, _⟩ := H
  exact ⟨raw.symm, raw.trans raw.symm, support, typed, formation, code,
    Related.symm henv bridge, Related.left_diagonal bridge⟩

end Lean4Lean.AnchoredSemantics
