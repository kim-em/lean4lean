import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree

/-! Bare native constants cannot reach a saturated terminal without first
observing a formal binder. Atom selection therefore retains the identical
native payload, rather than manufacturing a new terminal observation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics

/-- This is a literal profile-shape fact; it uses neither semantic typing
nor a source or target well-formedness premise. -/
theorem NativeConstantObservation.fn_profile
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {demand : Profile n}
    (observation : NativeConstantObservation env U registry target name levels demand) :
    ∃ (rank : Nat) (bound : n = rank + 1) (key : Key rank) (output : Atom rank),
      bound ▸ demand = Profile.fn key output := by
  have tree := observation.tree
  generalize hfoot : ([] : Footprint) = footprint at tree
  cases tree with
  | terminal leaf =>
    have impossible := leaf.saturated
    simp only [List.length_nil] at impossible
    omega
  | @binder rank arguments domain key output support packed domainFootprint
      bodyFootprint outside domainOrigin domainCode guard body pack covered =>
    exact ⟨rank, rfl, key, output, rfl⟩

/-- Every selected atom of the raw native demand is the whole demand. The
original finite telescope tree can consequently be reused unchanged. -/
theorem NativeConstantObservation.singleton_of_mem
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {demand : Profile n}
    (observation : NativeConstantObservation env U registry target name levels demand)
    {atom : Atom n} (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  obtain ⟨rank, rfl, key, output, equality⟩ := observation.fn_profile
  change demand = Profile.fn key output at equality
  cases equality
  have same : atom = .fn key output := List.mem_singleton.mp member
  exact same ▸ rfl

end Lean4Lean.AnchoredSource.Adapted
