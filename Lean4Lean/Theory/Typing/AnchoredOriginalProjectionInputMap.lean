import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionObserverReindex

/-! Finite value maps retain the original grade of a projected field.
Raising the output does not replace its major observer by a fabricated
higher-grade record observer. These maps contain no semantic callbacks.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive ProjectionInputMap (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : {m n : Nat} → Profile m → Profile n → Type where
  | select (member : atom ∈ input.atoms) :
      ProjectionInputMap env U registry target input (.singleton atom)
  | view (change : AtomView env U registry target first second) :
      ProjectionInputMap env U registry target (.singleton first) (.singleton second)
  | raise (input : Profile n) (bound : n ≤ N) :
      ProjectionInputMap env U registry target input (raiseProfile N bound input)
  | unpad (input : Profile n) :
      ProjectionInputMap env U registry target input.pad input
  | trans
      (first : ProjectionInputMap env U registry target input middle)
      (second : ProjectionInputMap env U registry target middle output) :
      ProjectionInputMap env U registry target input output

noncomputable def ProjectionInputMap.mapType
    (change : ProjectionInputMap env U registry target (input : Profile m) (output : Profile n)) :
    Profile m → Profile n :=
  match change with
  | .select _ => id
  | .view change => change.mapType
  | .raise _ bound => raiseProfile _ bound
  | .unpad _ => Profile.down
  | .trans first second => fun support => second.mapType (first.mapType support)

theorem ProjectionInputMap.term
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (change : ProjectionInputMap env U registry target input output)
    (related : Related env U registry target left right type input support) :
    Related env U registry target left right type output (change.mapType support) := by
  induction change with
  | select member => exact Related.singleton_of_mem related member
  | view change => exact change.termMap henv hscoped formed related
  | raise input bound => exact Related.raise henv bound related
  | unpad input => exact Related.unpad henv formed related
  | trans first second ihFirst ihSecond => exact ihSecond (ihFirst related)

noncomputable def ProjectionInputMap.mixed
    (henv : env.Ordered) (route : MixedInsertion env U target future ρ)
    (change : ProjectionInputMap env U registry target input output) :
    ProjectionInputMap env U registry future (input.rename ρ) (output.rename ρ) := by
  induction change with
  | select member =>
    simpa only [Profile.rename, Profile.singleton, Profile.mk, Profile.atoms, List.map_cons, List.map_nil] using
      ProjectionInputMap.select (env := env) (U := U) (registry := registry)
        (target := future) (List.mem_map.mpr ⟨_, member, rfl⟩)
  | view change =>
    simpa only [Profile.rename_singleton] using ProjectionInputMap.view (change.mixed henv route)
  | raise input bound =>
    simpa only [raiseProfile_rename] using
      ProjectionInputMap.raise (env := env) (U := U) (registry := registry)
        (target := future) (input.rename ρ) bound
  | unpad input =>
    simpa only [Profile.rename_pad] using
      ProjectionInputMap.unpad (env := env) (U := U) (registry := registry)
        (target := future) (input.rename ρ)
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

private noncomputable def chainSelect
    (chain : DomainChain env U registry target input left right)
    (member : atom ∈ input.atoms) :
    DomainChain env U registry target (.singleton atom) left right := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed code tail ih =>
    exact .step path (typed.singleton_of_mem member) formed code ih

private noncomputable def chainRaise
    (henv : env.Ordered) (bound : n ≤ N)
    (chain : DomainChain env U registry target (input : Profile n) left right) :
    DomainChain env U registry target (raiseProfile N bound input) left right := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed code tail ih =>
    exact .step path (Profile.HasType.raise bound typed) (Profile.HasType.raise_sort bound formed)
      (TypeRelated.raise henv bound code) ih

private theorem raiseProfile_map_atoms (bound : n ≤ N) (profile : Profile n) :
    raiseProfile N bound profile = profile.map (raiseAtom N bound) := by
  induction profile with
  | nil => exact raiseProfile_empty bound
  | cons atom rest ih =>
    change raiseProfile N bound ((Profile.singleton atom).union rest) = _
    rw [raiseProfile_union, raiseProfile_singleton, ih]
    rfl

/-- One actual primitive source leaf for one requested output atom.
Its original field request may have any grade, independently of the final
constructor argument grade. -/
structure ProjectionAtomRecipe
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (output : Atom n) where
  rank : Nat
  record : RecordData (Profile rank)
  name_eq : record.family.name = name
  request : DataRequest (Profile rank)
  member : (index, request) ∈ record.fields
  footprint : Footprint
  observation : Obs env U registry target locals σ major
    (.singleton (n := rank + 1) (.record record)) footprint
  change : ProjectionInputMap env U registry target request.input (.singleton output)
  alignment : DomainChain env U registry target (.singleton output) request.domain (assigned.subst σ)

/-- Extract recipes from the actual typed tree. Union follows literal
membership; view and raising transform the selected leaf's finite maps.
No outgoing recipe, family descriptor equality, or semantic field supplier
is assumed. -/
theorem ProjectionObs.atomRecipe
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (query : ProjectionObs env registry target node locals σ demand footprint)
    (resources : footprint.Available available)
    (member : atom ∈ demand.atoms) :
    ∃ recipe : ProjectionAtomRecipe env registry target node locals σ atom,
      recipe.footprint.Available available := by
  induction query with
  | field nameEq fieldMember majorObservation fieldCertificate typed alignment =>
    exact ⟨⟨_, _, nameEq, _, fieldMember, _, majorObservation,
      .select member, chainSelect alignment member⟩,
      fun i need present => resources i need (List.mem_append_left _ present)⟩
  | empty => cases member
  | union left right ihLeft ihRight =>
    rcases List.mem_append.mp member with member | member
    · exact ihLeft (fun i need present => resources i need (List.mem_append_left _ present)) member
    · exact ihRight (fun i need present => resources i need (List.mem_append_right _ present)) member
  | view child change ih =>
    cases List.mem_singleton.mp member
    obtain ⟨recipe, recipeResources⟩ := ih resources (List.mem_singleton_self _)
    exact ⟨{ recipe with
      change := .trans recipe.change (.view change)
      alignment := recipe.alignment.mapInput henv hscoped (.cons change .nil) }, recipeResources⟩
  | unpad child ih =>
    obtain ⟨recipe, recipeResources⟩ := ih resources (List.mem_map.mpr ⟨atom, member, rfl⟩)
    exact ⟨{ recipe with
      change := .trans recipe.change (by
        simpa only [Profile.pad_singleton] using
          (ProjectionInputMap.unpad (env := env) (U := U) (registry := registry)
            (target := target) (.singleton atom)))
      alignment := DomainChain.unpad henv (by
        simpa only [Profile.pad_singleton] using recipe.alignment) }, recipeResources⟩
  | raise child bound ih =>
    rw [show (raiseProfile _ bound _).atoms = _ from raiseProfile_map_atoms bound _] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨recipe, recipeResources⟩ := ih resources present
    exact ⟨{ recipe with
      change := by
        simpa only [raiseProfile_singleton] using
          (ProjectionInputMap.trans recipe.change (.raise (.singleton original) bound))
      alignment := by
        simpa only [raiseProfile_singleton] using (chainRaise henv bound recipe.alignment) }, recipeResources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
