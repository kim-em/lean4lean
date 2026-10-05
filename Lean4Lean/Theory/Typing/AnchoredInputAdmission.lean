import Lean4Lean.Theory.Typing.AnchoredViewTyping
import Lean4Lean.Theory.Typing.AnchoredInputSupport

/-! Admission transports its existing finite support through a paired input
view. The two interpretation premises are instantiated by the strict lower
rank of the function-input constructor. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Change only the input demand of an admitted key. Raw domain, anchor and
argument paths are retained; every semantic clause uses the same mapped
support. This helper asks for actual lower-rank profile interpretation laws. -/
theorem ProfileView.admissionMapWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {input : Profile n} {left right : VExpr}
    (view : ProfileView env U registry Γ key.input input)
    (hΓ : OnCtx Γ (env.IsType U))
    (code : ∀ {source target : Profile n} (v : ProfileView env U registry Γ source target)
      {l r : VExpr} {d : Profile n}, TypeRelated env U registry Γ l r d →
        TypeRelated env U registry Γ l r (v.mapType d))
    (term : OnCtx Γ (env.IsType U) →
      ∀ {source target : Profile n} (v : ProfileView env U registry Γ source target)
      {l r A : VExpr} {d : Profile n}, source.HasType d →
        Related env U registry Γ l r A source d →
          Related env U registry Γ l r A target (v.mapType d))
    (H : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ (inputKey key input) left right := by
  obtain ⟨rawAnchor, rawPair, support, typed, formation, domain, anchor, pair⟩ := H
  exact ⟨rawAnchor, rawPair, view.mapType support, view.mapType_typed typed,
    view.mapType_sort formation, code view domain,
    term hΓ view typed anchor, term hΓ view typed pair⟩

end Lean4Lean.AnchoredSemantics
