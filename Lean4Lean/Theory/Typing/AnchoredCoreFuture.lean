import Lean4Lean.Theory.Typing.AnchoredFunctionFuture

/-! A saturated term's chosen core persists under actual future insertions.
Function observations transport a single self-display; non-function code
observations retain their full future capability explicitly. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def CoreRelated (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {n : Nat} (Γ : List VExpr) (left right type : VExpr)
    (value typeProfile : Profile n) : Prop :=
  value.HasType typeProfile ∧ TypeRelated env U registry Γ type type typeProfile ∧
    match n, value with
    | 0, value => TypeRelated env U registry Γ left right value
    | n + 1, value => ∀ atom ∈ value.atoms,
        TermAtom env U registry (relations env U registry n) Γ left right type typeProfile atom

theorem TermAtom.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {typeProfile : Profile (n + 1)} {atom : Atom (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (W : FutureInsertion env U Γ Δ ρ)
    (h : TermAtom env U registry (relations env U registry n)
      Γ left right type typeProfile atom) :
    TermAtom env U registry (relations env U registry n)
      Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (typeProfile.rename ρ) (atom.rename ρ) := by
  cases atom with
  | ctor demand => exact RankedData.ConstructorRelation.future henv h W
  | record demand => exact RankedData.RecordRelation.future henv h W
  | family demand =>
    change TypeRelated env U registry Γ left right
      (.singleton (n := n + 1) (.family demand)) at h
    change TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ)
      (.singleton (n := n + 1) (.family (demand.rename ρ)))
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.rename] using
      TypeRelated.future henv W h
  | fn key output => exact FunctionBehavior.future henv hscoped W h
  | pad atom =>
    change Related env U registry Γ left right type (.singleton atom) typeProfile.down at h
    change Related env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (.singleton (atom.rename ρ)) (typeProfile.rename ρ).down
    simpa only [Profile.rename_singleton, Profile.down_rename] using
      Related.future henv W h
  | sort relevant =>
    change TypeRelated env U registry Γ left right (Profile.sort (n := n + 1) relevant) at h
    change TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ)
      (Profile.sort (n := n + 1) relevant)
    simpa only [Profile.rename_sort] using
      TypeRelated.future henv W h
  | pi A B domain rows =>
    change Profile n at domain
    change TypeRelated env U registry Γ left right (Profile.pi A B domain rows) at h
    change TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ)
      (Profile.pi (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows))
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi] using
      TypeRelated.future henv W h

theorem CoreRelated.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {value typeProfile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (W : FutureInsertion env U Γ Δ ρ)
    (h : CoreRelated env U registry Γ left right type value typeProfile) :
    CoreRelated env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ) := by
  obtain ⟨ht, hc, hv⟩ := h
  refine ⟨Profile.rename_hasType_iff.mpr ht, TypeRelated.future henv W hc, ?_⟩
  cases n with
  | zero => exact TypeRelated.future henv W hv
  | succ n =>
    intro atom ha
    obtain ⟨oldAtom, hm, rfl⟩ := List.mem_map.mp ha
    exact TermAtom.future henv hscoped W (hv oldAtom hm)

end Lean4Lean.AnchoredSemantics
