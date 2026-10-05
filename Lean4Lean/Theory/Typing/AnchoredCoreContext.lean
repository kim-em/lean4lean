import Lean4Lean.Theory.Typing.AnchoredCoreFuture
import Lean4Lean.Theory.Typing.AnchoredContextCongruence
import Batteries.Tactic.OpenPrivate

/-! Context conversion preserves the particular unsaturated term core.
No new saturation frame is chosen when transporting a native replay core. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
open private function_context context_congruence from
  Lean4Lean.Theory.Typing.AnchoredContextCongruence
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ Δ : List VExpr} {left right type : VExpr}

theorem TermAtom.convertContext
    {support : Profile (n + 1)} {atom : Atom (n + 1)}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Δ)
    (related : TermAtom env U registry (relations env U registry n)
      Γ left right type support atom) :
    TermAtom env U registry (relations env U registry n)
      Δ left right type support atom := by
  cases atom with
  | fn key output =>
    have lower := context_congruence env U registry henv n
    exact function_context henv lower.1 lower.2 conversion related
  | pad atom => exact Related.convertContext henv conversion related
  | sort relevant =>
    change TypeRelated env U registry Γ left right (Profile.sort (n := n + 1) relevant) at related
    exact TypeRelated.convertContext henv conversion related
  | pi A B domain rows =>
    change Profile n at domain
    change TypeRelated env U registry Γ left right (Profile.pi A B domain rows) at related
    exact TypeRelated.convertContext henv conversion related
  | family data =>
    change TypeRelated env U registry Γ left right
      (Profile.singleton (n := n + 1) (AtomData.family data)) at related
    exact TypeRelated.convertContext henv conversion related
  | ctor data => exact RankedData.ConstructorRelation.context henv (.single conversion) related
  | record data => exact RankedData.RecordRelation.context henv (.single conversion) related

theorem TermAtom.context
    {support : Profile (n + 1)} {atom : Atom (n + 1)}
    (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : TermAtom env U registry (relations env U registry n)
      Γ left right type support atom) :
    TermAtom env U registry (relations env U registry n)
      Δ left right type support atom := by
  induction chain with
  | refl => exact related
  | tail _ edge ih => exact ih.convertContext henv edge

theorem CoreRelated.convertContext
    {value support : Profile n}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Δ)
    (related : CoreRelated env U registry Γ left right type value support) :
    CoreRelated env U registry Δ left right type value support := by
  obtain ⟨typed, code, values⟩ := related
  refine ⟨typed, code.convertContext henv conversion, ?_⟩
  cases n with
  | zero => exact TypeRelated.convertContext henv conversion values
  | succ n => exact fun atom member => (values atom member).convertContext henv conversion

theorem CoreRelated.context
    {value support : Profile n}
    (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : CoreRelated env U registry Γ left right type value support) :
    CoreRelated env U registry Δ left right type value support := by
  induction chain with
  | refl => exact related
  | tail _ edge ih => exact ih.convertContext henv edge

end Lean4Lean.AnchoredSemantics
