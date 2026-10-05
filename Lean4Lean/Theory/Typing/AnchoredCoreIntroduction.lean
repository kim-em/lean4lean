import Lean4Lean.Theory.Typing.AnchoredCoreFuture

/-! A concrete unsaturated core supplies its future-closed term observation.
This is used to recover an admitted function anchor from a chosen core without
requiring the private assigned type or operands to descend to the base. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem CoreRelated.related
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {value support : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (H : CoreRelated env U registry Γ left right type value support) :
    Related env U registry Γ left right type value support := by
  cases n with
  | zero =>
    intro atom member Δ ρ future
    refine .inr ⟨Δ, .refl, .refl (future.targetWF henv), ?_⟩
    simp only [lift'_refl, Profile.rename_refl]
    have moved := H.future henv hscoped future
    refine ⟨?_, moved.2.1, ?_⟩
    · exact moved.1.singleton_of_mem (List.mem_map_of_mem member)
    · intro Ω τ later requested requestedMember
      have source := moved.2.2 Ω τ later requested
      apply source
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp requestedMember
      have eq : old = atom.rename ρ := List.mem_singleton.mp oldMember
      subst old
      exact List.mem_map_of_mem (List.mem_map_of_mem member)
  | succ n =>
    intro atom member Δ ρ future
    refine .inr ⟨Δ, .refl, .refl (future.targetWF henv), ?_⟩
    simp only [lift'_refl, Profile.rename_refl]
    have moved := H.future henv hscoped future
    refine ⟨moved.1.singleton_of_mem (List.mem_map_of_mem member), moved.2.1, ?_⟩
    intro requested requestedMember
    have eq : requested = atom.rename ρ := List.mem_singleton.mp requestedMember
    subst requested
    exact moved.2.2 _ (List.mem_map_of_mem member)

end Lean4Lean.AnchoredSemantics
