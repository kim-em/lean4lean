import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain
import Lean4Lean.Theory.Typing.AnchoredSourcePruning

/-! Source application after both original children return finite adapters.
The function row retained here is an actual computational observation. Its
argument may have a different computational demand, connected by a finite
adapter. No source type annotation or semantic producer is stored in a node.
These nodes are the concrete extension required by the source grammar; they
are not claimed to be constructors of the earlier `Obs` datatype. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Extract the selected function row's admission in the original target
context. Its support is chosen at the original literal caller Pi before
opening proof saturation; only raw typing is retracted afterwards. -/
theorem Related.fn_seed_literal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right A B : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right (.forallE A B)
      (Profile.fn key output) support) :
    Admitted env U registry Γ key key.anchor key.anchor := by
  obtain ⟨baseSupport, baseTyped, baseFormed, _, bridge⟩ :=
    related.fn_domain_alignment henv hscoped hΓ
  have baseCode := TypeRelated.left_diagonal bridge
  have original := related (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at original
  rcases original with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn (key.rename ρ) (output.rename ρ))
      (List.mem_singleton_self _)
    obtain ⟨seed, _⟩ := behavior
    obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := seed
    have targetCode := baseCode.future henv insertion.toFuture
    have targetTyped := (Profile.rename_hasType_iff (ρ := ρ)).mpr baseTyped
    have changed := Related.retag henv targetTyped targetCode anchor
    have baseAnchor := Related.absorb henv insertion changed
    obtain ⟨embedding, embeddingMap⟩ := insertion.toEmbedding henv
    have baseRaw := raw.subst henv embedding.typed hΓ
    simp only [Key.rename, ← embeddingMap, embedding.leftInv] at baseRaw
    exact ⟨baseRaw, baseRaw, baseSupport, baseTyped, baseFormed, baseCode,
      baseAnchor, baseAnchor⟩

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The proposed adapted application constructor, with genuine source children
and its actual target guard. The output is the raw function row's output. -/
structure AdapterApplication (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr)
    (locals : List Nat) (σ : Subst) (function argument : VExpr)
    (output : Atom n) (footprint : Footprint) where
  key : Key n
  functionFootprint : Footprint
  functionObservation : Obs env U registry Γ locals σ function
    (Profile.fn key output) functionFootprint
  argumentDemand : Profile n
  argumentFootprint : Footprint
  argumentObservation : Obs env U registry Γ locals σ argument
    argumentDemand argumentFootprint
  arguments : NormalProfileAdapter env U registry Γ argumentDemand key.input
  admitted : Admitted env U registry Γ key (argument.subst σ) (argument.subst σ)
  footprint_eq : footprint = functionFootprint ++ argumentFootprint

/-- Syntactic normalization first selects an actual function row and composes
only its input adapter with the argument adapter. The output adapter remains
outside the application. The actual admission is filled by the closed target
adapter interpreter, using the selected function row's anchor admission. -/
structure ApplicationFactor (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr)
    (locals : List Nat) (σ : Subst) (function argument : VExpr)
    (requestedKey : Key n) (requestedOutput : Atom n)
    (functionDemand : Profile (n + 1)) (argumentDemand : Profile n) (functionFootprint argumentFootprint : Footprint) where
  key : Key n
  output : Atom n
  rawOrigin : Atom (n + 1)
  origin : rawOrigin ∈ functionDemand.atoms
  normalOrigin : AdapterNormal.atom rawOrigin = .fn key output
  selectedFootprint : Footprint
  functionObservation : Obs env U registry Γ locals σ function
    (Profile.fn key output) selectedFootprint
  selected : selectedFootprint.Atomizes functionFootprint
  argumentObservation : Obs env U registry Γ locals σ argument
    argumentDemand argumentFootprint
  argumentAdapter : NormalProfileAdapter env U registry Γ argumentDemand key.input
  keys : KeyProgram env U registry Γ key (AdapterNormal.key requestedKey)
  outputAdapter : NormalAtomAdapter env U registry Γ output requestedOutput

/-- Both adapted children normalize at the actual returned function row.
The argument cut is finite syntax, recursively composed below that row's
rank. In particular this does not request an argument observation at an
intermediate demand. -/
theorem Obs.factor_application
    (henv : env.Ordered)
    (functionObservation : Obs env U registry Γ locals σ function
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : NormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : Obs env U registry Γ locals σ argument
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : NormalProfileAdapter env U registry Γ argumentDemand requestedKey.input) :
    Nonempty (ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint) := by
  obtain ⟨normal, member, ⟨adapter⟩⟩ :=
    functionAdapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨key, output, normalOrigin, ⟨keys⟩, ⟨result⟩⟩ := adapter.fn_inv
  obtain ⟨selected⟩ := functionObservation.atom originalMember
  have fixed : AdapterNormal.atom (n := n + 1) (.fn key output) = .fn key output := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key key) (AdapterNormal.atom output) =
    AtomData.fn key output at fixed
  have keyFixed := (AtomData.fn.inj fixed).1
  have outputFixed := (AtomData.fn.inj fixed).2
  have inputFixed : AdapterNormal.profile key.input = key.input := congrArg KeyData.input keyFixed
  have selectedObservation := Obs.view selected.observation (AdapterNormal.view henv original)
  rw [normalOrigin] at selectedObservation
  have arguments : NormalProfileAdapter env U registry Γ argumentDemand key.input := by
    change ProfileAdapter env U registry Γ (AdapterNormal.profile argumentDemand)
      (AdapterNormal.profile key.input)
    rw [inputFixed]
    exact ProfileAdapter.comp argumentAdapter keys.arguments
  have result' : NormalAtomAdapter env U registry Γ output requestedOutput := by
    change AtomAdapter env U registry Γ (AdapterNormal.atom output) (AdapterNormal.atom requestedOutput)
    rw [outputFixed]
    exact result
  exact ⟨{
    key := key
    output := output
    rawOrigin := original
    origin := originalMember
    normalOrigin := normalOrigin
    selectedFootprint := selected.footprint
    functionObservation := selectedObservation
    selected := selected.atomizes
    argumentObservation := argumentObservation
    argumentAdapter := arguments
    keys := keys
    outputAdapter := result' }⟩

/-- This merely installs a concrete guard; it does not ask an arbitrary raw
conversion to produce semantic evidence. -/
def ApplicationFactor.close
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (admitted : Admitted env U registry Γ factor.key
      (argument.subst σ) (argument.subst σ)) :
    AdapterApplication env U registry Γ locals σ function argument factor.output
      (factor.selectedFootprint ++ argumentFootprint) where
  key := factor.key
  functionFootprint := factor.selectedFootprint
  functionObservation := factor.functionObservation
  argumentDemand := argumentDemand
  argumentFootprint := argumentFootprint
  argumentObservation := factor.argumentObservation
  arguments := factor.argumentAdapter
  admitted := admitted
  footprint_eq := rfl

/-- The old function row's concrete self-admission supplies the endpoint
support for the contravariant argument cut. No new source-domain observation
or interpretation of a stored typing derivation is requested. -/
theorem ApplicationFactor.admitted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (seed : Admitted env U registry Γ factor.key factor.key.anchor factor.key.anchor)
    (requested : Admitted env U registry Γ requestedKey
      (argument.subst σ) (argument.subst σ)) :
    Admitted env U registry Γ factor.key (argument.subst σ) (argument.subst σ) := by
  exact factor.keys.pull henv hscoped hΓ seed
    (AdapterNormal.normalizeAdmission henv hscoped hΓ requested)

/-- Close the normalized source application with the actual existing
requested admission and the selected function's self-admission. -/
def ApplicationFactor.realize
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (seed : Admitted env U registry Γ factor.key factor.key.anchor factor.key.anchor)
    (requested : Admitted env U registry Γ requestedKey
      (argument.subst σ) (argument.subst σ)) :
    AdapterApplication env U registry Γ locals σ function argument factor.output
      (factor.selectedFootprint ++ argumentFootprint) :=
  factor.close (factor.admitted henv hscoped hΓ seed requested)

/-- The guard producer uses the selected atom of the actual original
function-child relation. Its proof frame is discharged by `fn_seed_literal`. -/
def ApplicationFactor.realize_related
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (related : Related env U registry Γ left right (.forallE A B) functionDemand support)
    (requested : Admitted env U registry Γ requestedKey
      (argument.subst σ) (argument.subst σ)) :
    AdapterApplication env U registry Γ locals σ function argument factor.output
      (factor.selectedFootprint ++ argumentFootprint) := by
  have raw := related.singleton_of_mem factor.origin
  have normalized := (AdapterNormal.view henv factor.rawOrigin).termMap henv hscoped hΓ raw
  generalize hsupport : (AdapterNormal.view (U := U) (registry := registry)
    (Γ := Γ) henv factor.rawOrigin).mapType support = newSupport at normalized
  rw [factor.normalOrigin] at normalized
  exact factor.realize henv hscoped hΓ
    (normalized.fn_seed_literal henv hscoped hΓ) requested

/-- Selection only atomizes existing needs. Argument demands and their whole
source observations are retained, even when their adapter discards atoms. -/
theorem ApplicationFactor.available
    {available : Valuation}
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    (factor.selectedFootprint ++ argumentFootprint).Available
      (Valuation.atomize available) := by
  intro index need member
  rcases List.mem_append.mp member with member | member
  · exact factor.selected.available functionAvailable index need member
  · exact argumentAvailable.atomize index need member

/-- With the source valuation invariant, factoring uses the same fixed
available valuation, including beneath a previously packed binder. -/
theorem ApplicationFactor.available_closed
    {available : Valuation}
    (factor : ApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint)
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available)
    (closed : available.AtomClosed) :
    (factor.selectedFootprint ++ argumentFootprint).Available available :=
  (factor.available functionAvailable argumentAvailable).of_atomize closed

end Lean4Lean.AnchoredSource
