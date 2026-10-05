import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredAtomActionLive

/-! Generalized input programs retain genuine frozen-anchor admissions. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
open private sortable_atom_live from Lean4Lean.Theory.Typing.AnchoredAtomActionLive
set_option backward.isDefEq.respectTransparency false

theorem GeneralAtomAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact live
  | _, _, _, .code action formed => exact sortable_atom_live (action.preservesSort formed)
  | _ + 1, _, _, .fn keys result =>
    exact ⟨keys.forward henv hscoped hΓ live.1, result.live henv hscoped hΓ live.2⟩
  | _ + 1, _, _, .pad child => exact child.live henv hscoped hΓ live
termination_by n

theorem GeneralProfileAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (adapter : GeneralProfileAdapter env U registry Γ p q)
    (live : Profile.Live env U registry Γ p) : Profile.Live env U registry Γ q := by
  intro atom member
  obtain ⟨original, originalMember, ⟨entry⟩⟩ := adapter.origin member
  exact entry.live henv hscoped hΓ (live original originalMember)

theorem GeneralNormalAtomAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : GeneralNormalAtomAdapter env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  have normalized := (AdapterNormal.view henv a).live henv hscoped hΓ live
  have output := GeneralAtomAdapter.live henv hscoped hΓ adapter normalized
  exact ((AdapterNormal.view henv b).inverse henv).live henv hscoped hΓ output

end Lean4Lean.AnchoredSemantics
