import Lean4Lean.Theory.Typing.AnchoredAtomAction
import Lean4Lean.Theory.Typing.AnchoredGeneralGradedAdapters

/-! Every finite value action is a general directional adapter. Sortable
code endpoints are already canonical; function keys retain their normalized
identity while the exact lower output action is embedded recursively. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def AtomAction.toGeneralAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (action : AtomAction env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Γ a b := by
  match n, a, b, action with
  | _, _, _, .view v => exact v.toGeneralAdapter henv hscoped hΓ
  | _, _, _, .code leaf formed =>
    change GeneralAtomAdapter env U registry Γ (AdapterNormal.atom _) (AdapterNormal.atom _)
    rw [AdapterNormal.atom_sortable formed, AdapterNormal.atom_sortable (leaf.preservesSort formed)]
    exact .code leaf formed
  | _ + 1, _, _, .fn key child =>
    exact .fn (.refl (AdapterNormal.key key)) (child.toGeneralAdapter henv hscoped hΓ)
  | _ + 1, _, _, .pad child =>
    exact GeneralNormalAtomAdapter.pad henv hscoped hΓ (child.toGeneralAdapter henv hscoped hΓ)
  | _, _, _, .comp first second =>
    exact (first.toGeneralAdapter henv hscoped hΓ).comp (second.toGeneralAdapter henv hscoped hΓ)
termination_by sizeOf action

end Lean4Lean.AnchoredSemantics
