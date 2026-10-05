import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterEmbedding
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterComposition
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterInterpretation
import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- The intermediate endpoints are fixed syntax, so cutting two adapters
does not create a new demand for an intermediate type capability. -/
abbrev GeneralNormalAtomAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (a b : Atom n) :=
  GeneralAtomAdapter env U registry Γ (AdapterNormal.atom a) (AdapterNormal.atom b)

abbrev GeneralNormalProfileAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (p q : Profile n) :=
  GeneralProfileAdapter env U registry Γ (AdapterNormal.profile p) (AdapterNormal.profile q)

noncomputable def GeneralNormalAtomAdapter.comp
    (first : GeneralNormalAtomAdapter env U registry Γ a b)
    (second : GeneralNormalAtomAdapter env U registry Γ b c) :
    GeneralNormalAtomAdapter env U registry Γ a c := GeneralAtomAdapter.comp first second

noncomputable def GeneralNormalProfileAdapter.comp
    (first : GeneralNormalProfileAdapter env U registry Γ p q)
    (second : GeneralNormalProfileAdapter env U registry Γ q r) :
    GeneralNormalProfileAdapter env U registry Γ p r := GeneralProfileAdapter.comp first second

noncomputable def GeneralNormalAtomAdapter.future
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (adapter : GeneralNormalAtomAdapter env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  simpa only [GeneralNormalAtomAdapter, AdapterNormal.atom_rename] using GeneralAtomAdapter.future henv W adapter

noncomputable def GeneralNormalProfileAdapter.future
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (adapter : GeneralNormalProfileAdapter env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Δ (p.rename ρ) (q.rename ρ) := by
  simpa only [GeneralNormalProfileAdapter, AdapterNormal.profile_rename] using GeneralProfileAdapter.future henv W adapter

theorem GeneralNormalAtomAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {a b : Atom n}
    (adapter : GeneralNormalAtomAdapter env U registry Γ a b)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : (Profile.singleton b).HasType new)
    (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A (.singleton a) old) :
    Related env U registry Γ l r A (.singleton b) new := by
  let leftView := AdapterNormal.view (U := U) (registry := registry) (Γ := Γ) henv a
  let rightView := AdapterNormal.view (U := U) (registry := registry) (Γ := Γ) henv b
  have normalized := GeneralAtomAdapter.termMap adapter henv hscoped hΓ (rightView.mapType_typed typed)
    (rightView.codeMap henv hscoped code) (leftView.termMap henv hscoped hΓ related)
  exact Related.retag henv typed code
    ((rightView.inverse henv).termMap henv hscoped hΓ normalized)

theorem GeneralNormalProfileAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {p q : Profile n}
    (adapter : GeneralNormalProfileAdapter env U registry Γ p q)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : q.HasType new) (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A p old) :
    Related env U registry Γ l r A q new := by
  apply Related.of_singletons
  intro atom member
  obtain ⟨origin, originMember, ⟨entry⟩⟩ := adapter.origin (List.mem_map.mpr ⟨atom, member, rfl⟩)
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp originMember
  exact GeneralNormalAtomAdapter.termMap entry henv hscoped hΓ (typed.singleton_of_mem member) code
    (related.singleton_of_mem originalMember)

noncomputable def GeneralNormalAtomAdapter.mixed
    (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    (adapter : GeneralNormalAtomAdapter env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  simpa only [GeneralNormalAtomAdapter, AdapterNormal.atom_rename] using GeneralAtomAdapter.mixed henv W adapter

noncomputable def GeneralNormalProfileAdapter.mixed
    (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    (adapter : GeneralNormalProfileAdapter env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Δ (p.rename ρ) (q.rename ρ) := by
  simpa only [GeneralNormalProfileAdapter, AdapterNormal.profile_rename] using GeneralProfileAdapter.mixed henv W adapter

noncomputable def NormalAtomAdapter.toGeneral
    (adapter : NormalAtomAdapter env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Γ a b := AtomAdapter.toGeneral adapter

noncomputable def NormalProfileAdapter.toGeneral
    (adapter : NormalProfileAdapter env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Γ p q := ProfileAdapter.toGeneral adapter

noncomputable def AtomView.toGeneralAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (view : AtomView env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Γ a b :=
  NormalAtomAdapter.toGeneral (view.toAdapter henv hscoped hΓ)

noncomputable def ProfileView.toGeneralAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (view : ProfileView env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Γ p q :=
  NormalProfileAdapter.toGeneral (view.toAdapter henv hscoped hΓ)

end Lean4Lean.AnchoredSemantics
