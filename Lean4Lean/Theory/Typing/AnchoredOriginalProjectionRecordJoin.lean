import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSeededFrame
import Lean4Lean.Theory.Typing.AnchoredRecordFieldJoin

/-! A returned field recipe observes the common source major and retains
only finite target adapters, domain chains and the newly fixed field seed.
It can therefore join with another field recipe without inventing original
projection typings for the new major.
-/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem actualTransport (henv : env.Ordered) :
    LowerTransport env U (relations env U registry n) :=
  ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩

private theorem mixedEqBack (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : env.IsDefEq U Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)) :
    env.IsDefEq U Γ left right type := by
  induction route generalizing left right type with
  | proof insertion =>
    obtain ⟨embedding, map⟩ := insertion.toEmbedding henv
    have result := h.subst henv embedding.typed (hΓ₀ := embedding.baseWF)
    simpa only [← map, embedding.leftInv] using result
  | context chain =>
    apply (chain.symm henv).eq henv
    simpa only [lift'_refl] using h
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp] using h

theorem admission_mixedBack (henv : env.Ordered) (hscoped : registry.Scoped)
    (route : MixedInsertion env U Γ Δ ρ)
    (admission : RequestAdmission env U (relations env U registry n) Δ
      (request.rename ρ) (left.lift' ρ) (right.lift' ρ)) :
    RequestAdmission env U (relations env U registry n) Γ request left right := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admission
  exact ⟨mixedEqBack henv route anchor, mixedEqBack henv route pair,
    Profile.rename_hasType_iff.mp typed,
    Profile.rename_hasType_iff.mp (by simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using formed),
    route.codeBack henv hscoped code, route.termBack henv first, route.termBack henv last⟩

private noncomputable def chainMixed (henv : env.Ordered)
    (route : MixedInsertion env U Γ Δ ρ)
    (chain : DomainChain env U registry Γ input left right) :
    DomainChain env U registry Δ (input.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed code tail ih =>
    exact .step (route.path henv path) (Profile.rename_hasType_iff.mpr typed)
      (by simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed) (route.code henv code) ih

/-- Keep one actual registered field origin, and retag its admission to the
constructor's complete field request. The chosen family type code is not
changed or hidden inside the new value descriptor. -/
theorem RecordWitness.retagSingle
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr}
    {demand : RecordData (Profile n)} {oldRequest request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : RecordWitness env U registry (relations env U registry n) Γ left right type demand)
    (member : (index, oldRequest) ∈ demand.fields)
    (adapter : NormalProfileAdapter env U registry Γ oldRequest.input request.input)
    (alignment : DomainChain env U registry Γ request.input oldRequest.domain request.domain)
    (seed : RequestAdmission env U (relations env U registry n) Γ request
      (.proj demand.family.name index left) (.proj demand.family.name index left))
    (meaningful : request.input.Nonempty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type demand.family.name [(index, request)]) ∧
    RequestAdmission env U (relations env U registry n) Γ request
      (.proj demand.family.name index left) (.proj demand.family.name index right) := by
  have pair := witness.fields.map_member member
  have seed' := admission_transport henv (actualTransport henv) witness.insertion seed
  have adapter' : NormalProfileAdapter env U registry witness.context
      ((oldRequest.rename witness.map).input) ((request.rename witness.map).input) := by
    simpa only [NormalProfileAdapter, DataRequest.rename, DataRequest.map, KeyData.map, AdapterNormal.profile_rename] using
      adapter.mixed henv witness.insertion
  have alignment' := chainMixed henv witness.insertion alignment
  have joined := RequestAdmission.retagField henv hscoped
    (witness.insertion.targetWF henv witness.baseWF) adapter' alignment' seed' pair
  constructor
  · refine ⟨{
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
  · exact admission_mixedBack henv hscoped witness.insertion joined

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- This returned source query needs no synthetic source projection child.
Its field request is exactly the one fixed by the typed argument frame. -/
structure RecordFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) where
  oldDemand : RecordData (Profile n)
  name_eq : oldDemand.family.name = name
  oldRequest : DataRequest (Profile n)
  member : (index, oldRequest) ∈ oldDemand.fields
  footprint : Footprint
  observation : Obs env U registry target locals σ major
    (.singleton (n := n + 1) (.record oldDemand)) footprint
  adapter : NormalProfileAdapter env U registry target oldRequest.input request.input
  alignment : DomainChain env U registry target request.input oldRequest.domain request.domain
  seed : RankedData.RequestAdmission env U (relations env U registry n) target request
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  meaningful : request.input.Nonempty

/-- The original major theorem transfers the recipe's actual major child.
The returned seed and witness are constructed from that answer, not supplied
as independent per-field packets by the caller. -/
theorem RecordFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (query : RecordFieldRecipe env U registry target locals σ left name index request)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : query.footprint.Available available) :
    ∃ next : RecordFieldRecipe env U registry target locals τ right name index request,
      next.footprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name [(index, request)]) := by
  have transfer : GradedTransfer env U registry target locals σ τ available left right type :=
    (fundamental target locals σ τ available closed formed substitutions tails).1
  obtain ⟨answer⟩ := transfer query.observation resources
  obtain ⟨footprint, ⟨observation⟩, nextResources⟩ :=
    answer.observation.record_of_adapter henv answer.bound answer.adapter answer.resultAvailable closed
  have records := (answer.requestedRelated henv formed).recordRelation henv hscoped formed
  obtain ⟨witness⟩ := records target .refl (.refl formed)
  have rename : query.oldDemand.rename .refl = query.oldDemand := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj query.oldDemand.family.name index (left.subst σ))
      (.proj query.oldDemand.family.name index (left.subst σ)) := by
    simpa only [query.name_eq, subst] using query.seed
  obtain ⟨joined, pair⟩ := witness.retagSingle henv hscoped query.member
    query.adapter query.alignment seed query.meaningful
  obtain ⟨anchor, raw, typed, supportFormed, code, first, last⟩ := pair
  let next : RecordFieldRecipe env U registry target locals τ right name index request := {
    oldDemand := query.oldDemand, name_eq := query.name_eq, oldRequest := query.oldRequest
    member := query.member, footprint := footprint, observation := observation
    adapter := query.adapter, alignment := query.alignment, meaningful := query.meaningful
    seed := by
      simpa only [query.name_eq, subst] using
        (show RankedData.RequestAdmission env U (relations env U registry n) target request
          (.proj query.oldDemand.family.name index (right.subst τ))
          (.proj query.oldDemand.family.name index (right.subst τ)) from
        ⟨anchor.trans raw, raw.hasType.2, typed, supportFormed, code,
          Related.trans henv hscoped first last, Related.trans henv hscoped (Related.symm henv last) last⟩) }
  exact ⟨next, nextResources, by simpa only [query.name_eq] using joined⟩

/-- The primitive nonempty projected constructor argument produces both
its actual application frame and its outgoing same-major field recipe.
The recipe's request is the frame's literal key and support; neither an
incoming semantic field packet nor an assumed request alignment is used. -/
theorem OriginalProjectionMetadata.seededFieldRecipe
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major A B : VExpr}
    (rule : OriginalProjectionRule sourceEnv U source name index major major A)
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target rule.leftNode locals σ demand request)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fieldFundamental : StateFundamental env registry context (.ref (.left rule.field)))
    (leftFundamental : DerivationFundamental env registry context rule.left)
    (rightFundamental : DerivationFundamental env registry context rule.right)
    (majorResources : query.packet.majorFootprint.Available available)
    (fieldResources : query.packet.fieldFootprint.Available available)
    (meaningful : request.input.Nonempty) {result : Profile n}
    (body : CodeCert env U registry target (Locals.push locals)
      (σ.cons ((VExpr.proj name index major).subst σ)) B result []) :
    ∃ frame : ProjectionSeededFrame env registry target rule.leftNode locals σ available B result,
      Nonempty (RecordFieldRecipe env U registry target locals σ major name index
        (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank))) := by
  let seed : ProjectionArgumentSeed env registry target rule.leftNode locals σ available := {
    rank := n, demand := request.input
    footprint := query.packet.majorFootprint ++ query.packet.fieldFootprint
    query := .field query.name_eq query.packet.member query.packet.majorObservation
      query.packet.fieldCertificate query.packet.typed query.packet.alignment
    resources := fun i need member => (List.mem_append.mp member).elim
      (majorResources i need) (fieldResources i need) }
  let collected : ProjectionFactoredArguments env registry target rule.leftNode locals σ available
      [] [] (max n seed.rank) :=
    ⟨n, by simp [seed], .empty, [], .empty, (fun _ _ member => nomatch member), .nil⟩
  let combined : ProjectionObs env registry target rule.leftNode locals σ
      ((raiseProfile collected.rank (Nat.le_trans (Nat.le_max_right _ _) collected.bound)
        seed.demand).union collected.input) (seed.footprint ++ collected.footprint) :=
    .union (.raise seed.query (Nat.le_trans (Nat.le_max_right _ _) collected.bound)) collected.query
  have combinedResources : (seed.footprint ++ collected.footprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim
      (seed.resources i need) (collected.resources i need)
  obtain ⟨answer⟩ := combined.projDF rule henv hscoped below closed formed context tails substitutions
    fieldFundamental leftFundamental rightFundamental combinedResources
  have raw : env.HasType U target ((VExpr.proj name index major).subst σ) (A.subst σ) :=
    (rule.leftNode.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  let frame : ProjectionSeededFrame env registry target rule.leftNode locals σ available B result := {
    seed := seed, required := [], outside := [], outsideResources := fun _ _ member => nomatch member
    collected := collected, support := answer.support, domainFootprint := answer.typeFootprint
    domain := answer.certificate, domainResources := answer.typeAvailable
    guard := ⟨answer.typed, answer.certificate.formed, .refl, answer.typeCode,
      ⟨raw, raw, _, answer.typed, answer.certificate.formed, answer.typeCode,
        answer.related, answer.related⟩⟩
    body := by simpa only [collected, raiseProfile_self] using body }
  refine ⟨frame, ⟨{
    oldDemand := demand, name_eq := query.name_eq, oldRequest := request
    member := query.packet.member, footprint := query.packet.majorFootprint
    observation := query.packet.majorObservation
    adapter := ?_, alignment := ?_, seed := frame.fieldSeedAdmission henv
    meaningful := ?_ }⟩⟩
  · simpa only [frame, ProjectionSeededFrame.key, ProjectionSeededFrame.input,
      collected, seed, raiseProfile_self, Profile.union, Profile.empty, Profile.mk,
      Profile.atoms, List.append_nil] using
      (show NormalProfileAdapter env U registry target request.input request.input from .refl _)
  · simpa only [frame, ProjectionSeededFrame.key, ProjectionSeededFrame.input,
      collected, seed, raiseProfile_self, Profile.union, Profile.empty, Profile.mk,
      Profile.atoms, List.append_nil] using query.packet.alignment
  · simpa only [frame, ProjectionSeededFrame.key, ProjectionSeededFrame.input,
      collected, seed, raiseProfile_self, Profile.union, Profile.empty, Profile.mk,
      Profile.atoms, List.append_nil] using meaningful

/-- A finite same-major join. Each field keeps its exact constructor
request, while its primitive source observer may use a different family
code descriptor. This pilot includes nonempty field recipes. -/
inductive RecordQuery (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr) (name : Name) :
    List (Nat × DataRequest (Profile n)) → Footprint → Type where
  | field (recipe : RecordFieldRecipe env U registry target locals σ major name index request) :
      RecordQuery env U registry target locals σ major name [(index, request)] recipe.footprint
  | union
      (first : RecordQuery env U registry target locals σ major name requests firstFootprint)
      (second : RecordQuery env U registry target locals σ major name requests' secondFootprint) :
      RecordQuery env U registry target locals σ major name (requests ++ requests')
        (firstFootprint ++ secondFootprint)

/-- Every branch reuses the same fixed original major theorem. Exact
field requests survive both source reconstruction and target amalgamation;
no stronger family query is inferred from an unrelated branch. -/
theorem RecordQuery.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {requests : List (Nat × DataRequest (Profile n))}
    {left right type : VExpr}
    (query : RecordQuery env U registry target locals σ left name requests footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (RecordQuery env U registry target locals τ right name requests nextFootprint) ∧
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
