import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionInputMap
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRecordJoin

/-! Per-atom field recipes preserve the constructor frame's exact domain,
anchor and support even when their source major observers have unrelated
family descriptors and grades.
-/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
open AnchoredSource.Adapted.OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

private theorem typedTransport (henv : env.Ordered) :
    LowerTransport env U (relations env U registry n) :=
  ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩

private noncomputable def chainMixedAt (henv : env.Ordered)
    (route : MixedInsertion env U Γ Δ ρ)
    (chain : DomainChain env U registry Γ input left right) :
    DomainChain env U registry Δ (input.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed code tail ih =>
    exact .step (route.path henv path) (Profile.rename_hasType_iff.mpr typed)
      (by simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed) (route.code henv code) ih

/-- Old and new field grades are independent. Only the finite input map
raises or lowers the field relation; its raw projection origin is retained. -/
theorem RecordWitness.retagSingleMapped
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr}
    {demand : RecordData (Profile m)} {oldRequest : DataRequest (Profile m)}
    {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : RecordWitness env U registry (relations env U registry m) Γ left right type demand)
    (member : (index, oldRequest) ∈ demand.fields)
    (change : ProjectionInputMap env U registry Γ oldRequest.input request.input)
    (alignment : DomainChain env U registry Γ request.input oldRequest.domain request.domain)
    (seed : RequestAdmission env U (relations env U registry n) Γ request
      (.proj demand.family.name index left) (.proj demand.family.name index left))
    (meaningful : request.input.Nonempty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type demand.family.name [(index, request)]) := by
  have old := witness.fields.map_member member
  have seed' := admission_transport henv (typedTransport henv) witness.insertion seed
  have change' := change.mixed henv witness.insertion
  have alignment' := chainMixedAt henv witness.insertion alignment
  obtain ⟨anchor, _, typed, supportFormed, code, first, _⟩ := seed'
  have last := change'.term henv hscoped (witness.insertion.targetWF henv witness.baseWF)
    old.2.2.2.2.2.2
  have joined : RequestAdmission env U (relations env U registry n) witness.context
      (request.rename witness.map)
      (.proj demand.family.name index (left.lift' witness.map))
      (.proj demand.family.name index (right.lift' witness.map)) :=
    ⟨anchor, alignment'.path.cast old.2.1, typed, supportFormed, code, first,
      alignment'.related henv typed code last⟩
  refine ⟨{
    meaningful := ⟨(index, request), List.mem_singleton_self _, meaningful⟩
    baseWF := witness.baseWF, context := witness.context, map := witness.map
    insertion := witness.insertion, info := witness.info, lookup := witness.lookup
    ctorDefinition := witness.ctorDefinition, ctorNative := witness.ctorNative
    ctorQuotient := witness.ctorQuotient
    bounded := ?_, leftType := witness.leftType, rightType := witness.rightType
    leftOrigins := ?_, rightOrigins := ?_, fields := .cons joined .nil }⟩
  · intro entry present
    cases List.mem_singleton.mp present
    exact witness.bounded (index, oldRequest) member
  · intro entry present
    cases List.mem_singleton.mp present
    obtain ⟨origin⟩ := witness.leftOrigins _ member
    exact ⟨{ origin with fieldPath := origin.fieldPath.trans alignment'.path }⟩
  · intro entry present
    cases List.mem_singleton.mp present
    obtain ⟨origin⟩ := witness.rightOrigins _ member
    exact ⟨{ origin with fieldPath := origin.fieldPath.trans alignment'.path }⟩

theorem FieldRecordWitness.admission
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name requests)
    (member : (index, request) ∈ requests) :
    RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index right) :=
  admission_mixedBack henv hscoped witness.insertion (witness.fields.map_member member)

def atomFieldRequests (index : Nat) (request : DataRequest (Profile n)) (atoms : List (Atom n)) :
    List (Nat × DataRequest (Profile n)) :=
  atoms.map (fun atom => (index, { request with input := .singleton atom }))

/-- Coalescing retains the exact frame request, including its support and
anchor. The raw origin comes from an actual selected row; every output atom
uses its own admission in the joined private world. -/
theorem FieldRecordWitness.coalesce
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name (atomFieldRequests index request request.input.atoms))
    (seed : RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index left))
    (meaningful : request.input.Nonempty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name [(index, request)]) := by
  obtain ⟨atom, member⟩ := List.exists_mem_of_ne_nil _ meaningful
  have present : (index, { request with input := .singleton atom }) ∈
      atomFieldRequests index request request.input.atoms := List.mem_map.mpr ⟨atom, member, rfl⟩
  have first := witness.admission henv hscoped present
  have pair : RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index right) := by
    obtain ⟨anchor, _, typed, supportFormed, code, anchorTerm, _⟩ := seed
    refine ⟨anchor, first.2.1, typed, supportFormed, code, anchorTerm, ?_⟩
    apply Related.of_singletons
    intro selected selectedMember
    exact (witness.admission henv hscoped
      (List.mem_map.mpr ⟨selected, selectedMember, rfl⟩)).2.2.2.2.2.2
  have shifted := admission_transport henv (typedTransport henv) witness.insertion pair
  refine ⟨{
    witness with
    meaningful := ⟨(index, request), List.mem_singleton_self _, meaningful⟩
    bounded := ?_, leftOrigins := ?_, rightOrigins := ?_, fields := .cons shifted .nil }⟩
  · intro entry entryMember
    cases List.mem_singleton.mp entryMember
    exact witness.bounded (index, { request with input := .singleton atom }) present
  · intro entry entryMember
    cases List.mem_singleton.mp entryMember
    exact witness.leftOrigins (index, { request with input := .singleton atom }) present
  · intro entry entryMember
    cases List.mem_singleton.mp entryMember
    exact witness.rightOrigins (index, { request with input := .singleton atom }) present

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure AtomFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) (atom : Atom n) where
  oldRank : Nat
  record : RecordData (Profile oldRank)
  name_eq : record.family.name = name
  oldRequest : DataRequest (Profile oldRank)
  member : (index, oldRequest) ∈ record.fields
  footprint : Footprint
  observation : Obs env U registry target locals σ major
    (.singleton (n := oldRank + 1) (.record record)) footprint
  change : ProjectionInputMap env U registry target oldRequest.input (.singleton atom)
  alignment : DomainChain env U registry target (.singleton atom) oldRequest.domain request.domain
  seed : RankedData.RequestAdmission env U (relations env U registry n) target
    { request with input := .singleton atom }
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)

/-- Every atom of the frame input has an extracted primitive source recipe.
This includes atoms originating in reconstructed dependent cuts, since the
frame's actual query is the union of those cuts with its original seed. -/
theorem ProjectionSeededFrame.atomRecipe
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {index : Nat} {major A B : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) A} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProjectionSeededFrame env registry target node locals σ available B result)
    {atom : Atom frame.collected.rank}
    (member : atom ∈ frame.input.atoms) :
    ∃ recipe : AtomFieldRecipe env U registry target locals σ major name index
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank)) atom,
      recipe.footprint.Available available := by
  obtain ⟨recipe, resources⟩ := frame.argumentQuery.atomRecipe henv hscoped frame.argumentResources member
  exact ⟨⟨recipe.rank, recipe.record, recipe.name_eq, recipe.request, recipe.member,
    recipe.footprint, recipe.observation, recipe.change, recipe.alignment,
    (frame.fieldSeedAdmission henv).singleton member⟩, resources⟩

/-- Source recipes are interpreted at the common ORIGINAL major typing,
not the independently inferred family typing of their projected children. -/
theorem AtomFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (query : AtomFieldRecipe env U registry target locals σ left name index request atom)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : query.footprint.Available available) :
    ∃ next : AtomFieldRecipe env U registry target locals τ right name index request atom,
      next.footprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name
        [(index, { request with input := .singleton atom })]) := by
  have transfer : GradedTransfer env U registry target locals σ τ available left right type :=
    (fundamental target locals σ τ available closed formed substitutions tails).1
  obtain ⟨answer⟩ := transfer query.observation resources
  obtain ⟨footprint, ⟨observation⟩, nextResources⟩ :=
    answer.observation.record_of_adapter henv answer.bound answer.adapter answer.resultAvailable closed
  have records := (answer.requestedRelated henv formed).recordRelation henv hscoped formed
  obtain ⟨witness⟩ := records target .refl (.refl formed)
  have rename : query.record.rename .refl = query.record := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := query.oldRank) .refl = id from funext Profile.rename_refl, RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target
      { request with input := .singleton atom }
      (.proj query.record.family.name index (left.subst σ))
      (.proj query.record.family.name index (left.subst σ)) := by
    simpa only [query.name_eq, subst] using query.seed
  obtain ⟨joined⟩ := witness.retagSingleMapped henv hscoped query.member query.change query.alignment seed
    (by intro h; cases h)
  obtain ⟨anchor, raw, typed, supportFormed, code, first, last⟩ :=
    joined.admission henv hscoped (List.mem_singleton_self _)
  let next : AtomFieldRecipe env U registry target locals τ right name index request atom := {
    oldRank := query.oldRank, record := query.record, name_eq := query.name_eq
    oldRequest := query.oldRequest, member := query.member
    footprint := footprint, observation := observation
    change := query.change, alignment := query.alignment
    seed := by
      simpa only [query.name_eq, subst] using
        (show RankedData.RequestAdmission env U (relations env U registry n) target
          { request with input := .singleton atom }
          (.proj query.record.family.name index (right.subst τ))
          (.proj query.record.family.name index (right.subst τ)) from
          ⟨anchor.trans raw, raw.hasType.2, typed, supportFormed, code,
            Related.trans henv hscoped first last,
            Related.trans henv hscoped (Related.symm henv last) last⟩) }
  exact ⟨next, nextResources, ⟨by simpa only [query.name_eq] using joined⟩⟩

inductive AtomFieldRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) :
    List (Atom n) → Footprint → Type where
  | nil : AtomFieldRows env U registry target locals σ major name index request [] []
  | cons
      (recipe : AtomFieldRecipe env U registry target locals σ major name index request atom)
      (tail : AtomFieldRows env U registry target locals σ major name index request atoms footprint) :
      AtomFieldRows env U registry target locals σ major name index request (atom :: atoms)
        (recipe.footprint ++ footprint)

/-- Construct all rows by traversing the frame's actual output atoms. -/
theorem ProjectionSeededFrame.atomRows
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {index : Nat} {major A B : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) A} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProjectionSeededFrame env registry target node locals σ available B result) :
    ∃ footprint, Nonempty (AtomFieldRows env U registry target locals σ major name index
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank)) frame.input.atoms footprint) ∧
      footprint.Available available := by
  suffices ∀ atoms, List.Subset atoms frame.input.atoms → ∃ footprint,
      Nonempty (AtomFieldRows env U registry target locals σ major name index
        (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank)) atoms footprint) ∧
      footprint.Available available from this _ (fun _ member => member)
  intro atoms
  induction atoms with
  | nil => intro _; exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons atom atoms ih =>
    intro included
    obtain ⟨recipe, resources⟩ := frame.atomRecipe henv hscoped (included List.mem_cons_self)
    obtain ⟨footprint, ⟨tail⟩, tailResources⟩ := ih (fun _ member => included (List.mem_cons_of_mem _ member))
    exact ⟨recipe.footprint ++ footprint, ⟨.cons recipe tail⟩,
      fun i need member => (List.mem_append.mp member).elim (resources i need) (tailResources i need)⟩

theorem AtomFieldRows.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (rows : AtomFieldRows env U registry target locals σ left name index request atoms footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (AtomFieldRows env U registry target locals τ right name index request atoms nextFootprint) ∧
      nextFootprint.Available available ∧
      (atoms ≠ [] → Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name
        (RankedData.atomFieldRequests index request atoms))) := by
  induction rows with
  | nil => exact ⟨[], ⟨.nil⟩, (fun _ _ member => nomatch member), fun nonempty => (nonempty rfl).elim⟩
  | @cons atom atoms footprint recipe tail ih =>
    obtain ⟨next, nextResources, ⟨first⟩⟩ := recipe.transfer original henv hscoped closed formed
      context tails substitutions fundamental
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨nextFootprint, ⟨nextRows⟩, tailResources, rest⟩ :=
      ih (fun i need member => resources i need (List.mem_append_right _ member))
    refine ⟨next.footprint ++ nextFootprint, ⟨.cons next nextRows⟩,
      (fun i need member => (List.mem_append.mp member).elim (nextResources i need) (tailResources i need)), ?_⟩
    intro _
    by_cases empty : atoms = []
    · subst atoms
      exact ⟨first⟩
    · obtain ⟨last⟩ := rest empty
      simpa only [RankedData.atomFieldRequests, List.map_cons, List.singleton_append] using
        first.append henv
          ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩ last

/-- A full field query stores exactly the requested frame key. Its finite
rows are derived from the typed argument tree, including dependent cuts. -/
structure WholeFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) where
  footprint : Footprint
  rows : AtomFieldRows env U registry target locals σ major name index request request.input.atoms footprint
  seed : RankedData.RequestAdmission env U (relations env U registry n) target request
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  meaningful : request.input.Nonempty

theorem ProjectionSeededFrame.wholeRecipe
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {index : Nat} {major A B : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) A} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProjectionSeededFrame env registry target node locals σ available B result)
    (meaningful : frame.input.Nonempty) :
    ∃ recipe : WholeFieldRecipe env U registry target locals σ major name index
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank)),
      recipe.footprint.Available available := by
  obtain ⟨footprint, ⟨rows⟩, resources⟩ := frame.atomRows henv hscoped
  exact ⟨⟨footprint, rows, frame.fieldSeedAdmission henv, meaningful⟩, resources⟩

/-- Source reconstruction and target coalescing both preserve the full
request. No atom's richer original major descriptor is substituted for it. -/
theorem WholeFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (query : WholeFieldRecipe env U registry target locals σ left name index request)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : query.footprint.Available available) :
    ∃ next : WholeFieldRecipe env U registry target locals τ right name index request,
      next.footprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name [(index, request)]) := by
  obtain ⟨footprint, ⟨rows⟩, nextResources, collected⟩ := query.rows.transfer original henv hscoped
    closed formed context tails substitutions fundamental resources
  obtain ⟨collected⟩ := collected query.meaningful
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj name index (left.subst σ)) (.proj name index (left.subst σ)) := by
    simpa only [subst] using query.seed
  obtain ⟨witness⟩ := collected.coalesce henv hscoped seed query.meaningful
  obtain ⟨anchor, raw, typed, supportFormed, code, first, last⟩ :=
    witness.admission henv hscoped (List.mem_singleton_self _)
  let next : WholeFieldRecipe env U registry target locals τ right name index request := {
    footprint := footprint, rows := rows, meaningful := query.meaningful
    seed := by
      simpa only [subst] using
        (show RankedData.RequestAdmission env U (relations env U registry n) target request
          (.proj name index (right.subst τ)) (.proj name index (right.subst τ)) from
          ⟨anchor.trans raw, raw.hasType.2, typed, supportFormed, code,
            Related.trans henv hscoped first last,
            Related.trans henv hscoped (Related.symm henv last) last⟩) }
  exact ⟨next, nextResources, ⟨witness⟩⟩

/-- A finite record query assembled from the full field requests produced
by its actual typed projected arguments. Family type code remains external
and can be attached with FieldRecordWitness.attachType. -/
inductive ProjectionRecordQuery (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr) (name : Name) :
    List (Nat × DataRequest (Profile n)) → Footprint → Type where
  | field (recipe : WholeFieldRecipe env U registry target locals σ major name index request) :
      ProjectionRecordQuery env U registry target locals σ major name [(index, request)] recipe.footprint
  | union
      (first : ProjectionRecordQuery env U registry target locals σ major name requests firstFootprint)
      (second : ProjectionRecordQuery env U registry target locals σ major name requests' secondFootprint) :
      ProjectionRecordQuery env U registry target locals σ major name (requests ++ requests')
        (firstFootprint ++ secondFootprint)

theorem ProjectionRecordQuery.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {requests : List (Nat × DataRequest (Profile n))}
    {left right type : VExpr}
    (query : ProjectionRecordQuery env U registry target locals σ left name requests footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionRecordQuery env U registry target locals τ right name requests nextFootprint) ∧
      nextFootprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name requests) := by
  induction query with
  | field recipe =>
    obtain ⟨next, nextResources, witness⟩ := recipe.transfer original henv hscoped closed formed
      context tails substitutions fundamental resources
    exact ⟨next.footprint, ⟨.field next⟩, nextResources, witness⟩
  | union first second ihFirst ihSecond =>
    obtain ⟨firstFootprint, ⟨firstQuery⟩, firstResources, ⟨firstWitness⟩⟩ :=
      ihFirst (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨secondFootprint, ⟨secondQuery⟩, secondResources, ⟨secondWitness⟩⟩ :=
      ihSecond (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨firstFootprint ++ secondFootprint, ⟨.union firstQuery secondQuery⟩,
      (fun i need member => (List.mem_append.mp member).elim
        (firstResources i need) (secondResources i need)),
      firstWitness.append henv
        ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩ secondWitness⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
