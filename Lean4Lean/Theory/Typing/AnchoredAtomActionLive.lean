import Lean4Lean.Theory.Typing.AnchoredAtomAction
import Lean4Lean.Theory.Typing.AnchoredLive

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

private theorem sortable_atom_live {atom : Atom n}
    (formed : (Profile.singleton atom).HasType (.sort relevant)) :
    Atom.Live env U registry Γ atom := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | record => trivial
    | fn key output =>
      obtain ⟨other, member, impossible⟩ := formed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    | pad atom =>
      change (Profile.singleton atom).pad.HasType (.sort relevant) at formed
      exact ih (by simpa only [Profile.down_sort] using formed.pad_inv)

theorem AtomAction.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  induction action with
  | view v => exact v.live henv hscoped hΓ live
  | code action formed => exact sortable_atom_live (action.preservesSort formed)
  | fn key child ih => exact ⟨live.1, ih live.2⟩
  | pad child ih => exact ih live
  | comp first second firstIH secondIH => exact secondIH (firstIH live)

end Lean4Lean.AnchoredSemantics
