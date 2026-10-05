import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionApplication

/-! Constructor adapters are applied after the raw projected argument has
been assembled at its actual natural type. Its earlier per-atom domain paths
remain unchanged; the final declared-domain chain is retained separately. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem transport (henv : env.Ordered) :
    LowerTransport env U (relations env U registry n) :=
  ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩

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

/-- Adapt a complete raw field request, then change its natural domain using
actual semantic alignment. The selected registered projection origins survive. -/
theorem FieldRecordWitness.retagSingle
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {oldRequest request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name requests)
    (member : (index, oldRequest) ∈ requests)
    (adapter : NormalProfileAdapter env U registry Γ oldRequest.input request.input)
    (alignment : DomainChain env U registry Γ request.input oldRequest.domain request.domain)
    (seed : RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index left))
    (meaningful : request.input.Nonempty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name [(index, request)]) := by
  have seed' := admission_transport henv (transport henv) witness.insertion seed
  have adapter' : NormalProfileAdapter env U registry witness.context
      ((oldRequest.rename witness.map).input) ((request.rename witness.map).input) := by
    simpa only [NormalProfileAdapter, DataRequest.rename, DataRequest.map, KeyData.map,
      AdapterNormal.profile_rename] using adapter.mixed henv witness.insertion
  have alignment' := chainMixed henv witness.insertion alignment
  have joined := RequestAdmission.retagField henv hscoped
    (witness.insertion.targetWF henv witness.baseWF) adapter' alignment' seed'
    (witness.fields.map_member member)
  refine ⟨{ witness with
    meaningful := ⟨(index, request), List.mem_singleton_self _, meaningful⟩
    bounded := ?_, leftOrigins := ?_, rightOrigins := ?_, fields := .cons joined .nil }⟩
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

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The application adapter cannot create an output atom from an empty raw
input. This proves the raw recipe is meaningful instead of assuming it. -/
theorem normalAdapter_nonempty
    (adapter : NormalProfileAdapter env U registry target input output)
    (meaningful : output.Nonempty) : input.Nonempty := by
  obtain ⟨atom, member⟩ := List.exists_mem_of_ne_nil _ meaningful
  obtain ⟨origin, original, _⟩ := adapter.origin (List.mem_map.mpr ⟨atom, member, rfl⟩)
  obtain ⟨first, present, _⟩ := List.mem_map.mp original
  intro empty
  have present : first ∈ input.atoms := present
  simpa only [empty, List.not_mem_nil] using present

/-- Selecting the actual seed from the merged input and raising its literal
application adapter yields the exact raised application request. -/
noncomputable def ProjectionSeededFrame.seedAdapter
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.proj name index major) A} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : ProjectionSeededFrame env registry target node locals σ available B result)
    {input : Profile frame.seed.rank}
    (adapter : NormalProfileAdapter env U registry target frame.seed.demand input) :
    NormalProfileAdapter env U registry target frame.input
      (raiseProfile frame.collected.rank
        (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound) input) := by
  have selection : NormalProfileAdapter env U registry target frame.input
      (raiseProfile frame.collected.rank
        (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound) frame.seed.demand) := by
    apply ProfileAdapter.select
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨old, List.mem_append_left _ present, rfl⟩
  exact selection.comp (adapter.raise henv hscoped formed _)

/-- Output of one actual projected argument step. The literal application
key is retained through a constructed adapter at the frame's resulting grade. -/
structure ProjectionApplicationResult
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation)
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) (key : Key k) (result : Profile n) where
  frame : ProjectionSeededFrame env registry target view.argument locals σ available
    view.codomainExpression result
  keyBound : k ≤ frame.collected.rank
  adapter : NormalProfileAdapter env U registry target frame.input
    (raiseProfile frame.collected.rank keyBound key.input)

private def transportSeedAdapter
    {first second : ProjectionArgumentSeed env registry target node locals σ available}
    {input : Profile k} (equal : first = second) (firstGrade : first.rank = k)
    (secondGrade : second.rank = k)
    (adapter : NormalProfileAdapter env U registry target second.demand (secondGrade.symm ▸ input)) :
    NormalProfileAdapter env U registry target first.demand (firstGrade.symm ▸ input) := by
  cases equal
  exact adapter

/-- No outgoing field metadata is an input: the actual argument query,
original result certificate and fixed original argument children build it. -/
theorem TypedSpineObs.projectedApplication
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) {key : Key k}
    (argument : TypedSpineObs env registry target root locals σ view.argument
      (.appArgument view.location) rawInput argumentFootprint)
    (arguments : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (argumentResources : argumentFootprint.Available available)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (view.codomainExpression.inst (.proj name index major)) result before)
    (resources : before.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry (projectionHead view.argument).route initial)
    (fieldFundamental : StateFundamental env registry initial (projectionHead view.argument).field)
    (majorFundamental : DerivationFundamental env registry initial (projectionHead view.argument).major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available) :
    Nonempty (ProjectionApplicationResult (env := env) registry target locals σ available
      view key result) := by
  obtain ⟨seed⟩ := argument.applicationSeed view arguments admitted argumentResources
  obtain ⟨prepared, seedEq⟩ := CodeCert.prepareProjectionApplication view seed certificate resources
  obtain ⟨frame, frameSeed, _, _, _⟩ := prepared.complete henv hscoped below initial
    calls fieldFundamental majorFundamental closed formed substitutions tails
  have exactSeed : frame.seed = seed.seed := frameSeed.trans (congrArg (fun x => x.seed) seedEq)
  have grade : frame.seed.rank = k := (congrArg (fun x => x.rank) exactSeed).trans seed.grade
  have seedAdapter : NormalProfileAdapter env U registry target frame.seed.demand
      (grade.symm ▸ key.input) := by
    exact transportSeedAdapter exactSeed grade seed.grade seed.adapter
  have resultAdapter := frame.seedAdapter henv hscoped formed seedAdapter
  have keyBound : k ≤ frame.collected.rank :=
    grade ▸ Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound
  refine ⟨⟨frame, keyBound, ?_⟩⟩
  cases grade
  exact resultAdapter

structure AdaptedFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) where
  rawRequest : DataRequest (Profile n)
  raw : WholeFieldRecipe env U registry target locals σ major name index rawRequest
  adapter : NormalProfileAdapter env U registry target rawRequest.input request.input
  alignment : DomainChain env U registry target request.input rawRequest.domain request.domain
  seed : RankedData.RequestAdmission env U (relations env U registry n) target request
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  meaningful : request.input.Nonempty

/-- The raw frame supplies all atom recipes. Only the actual application's
adapter, final declaration alignment and exact terminal seed are added. -/
theorem ProjectionSeededFrame.adaptedRecipe
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.proj name index major) A} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProjectionSeededFrame env registry target node locals σ available B result)
    (request : DataRequest (Profile frame.collected.rank))
    (adapter : NormalProfileAdapter env U registry target frame.input request.input)
    (alignment : DomainChain env U registry target request.input (A.subst σ) request.domain)
    (seed : RankedData.RequestAdmission env U (relations env U registry frame.collected.rank)
      target request ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (meaningful : request.input.Nonempty) :
    ∃ recipe : AdaptedFieldRecipe env U registry target locals σ major name index request,
      recipe.raw.footprint.Available available := by
  obtain ⟨raw, resources⟩ := frame.wholeRecipe henv hscoped (normalAdapter_nonempty adapter meaningful)
  exact ⟨⟨⟨frame.key, frame.support⟩, raw, adapter, alignment, seed, meaningful⟩, resources⟩

/-- Every original major call still receives a source observation constructed
from the raw projected argument. The finite adapter runs on the resulting
whole relation, after all independent raw field origins have been joined. -/
theorem AdaptedFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (query : AdaptedFieldRecipe env U registry target locals σ left name index request)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : query.raw.footprint.Available available) :
    ∃ next : AdaptedFieldRecipe env U registry target locals τ right name index request,
      next.raw.footprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name [(index, request)]) := by
  obtain ⟨raw, nextResources, ⟨witness⟩⟩ := query.raw.transfer original henv hscoped
    closed formed context tails substitutions fundamental resources
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj name index (left.subst σ)) (.proj name index (left.subst σ)) := by
    simpa only [subst] using query.seed
  obtain ⟨nextWitness⟩ := witness.retagSingle henv hscoped (List.mem_singleton_self _)
    query.adapter query.alignment seed query.meaningful
  obtain ⟨anchor, pair, typed, supportFormed, code, first, last⟩ :=
    nextWitness.admission henv hscoped (List.mem_singleton_self _)
  let next : AdaptedFieldRecipe env U registry target locals τ right name index request := {
    rawRequest := query.rawRequest, raw := raw, adapter := query.adapter
    alignment := query.alignment, meaningful := query.meaningful
    seed := by
      simpa only [subst] using
        (show RankedData.RequestAdmission env U (relations env U registry n) target request
          (.proj name index (right.subst τ)) (.proj name index (right.subst τ)) from
          ⟨anchor.trans pair, pair.hasType.2, typed, supportFormed, code,
            Related.trans henv hscoped first last,
            Related.trans henv hscoped (Related.symm henv last) last⟩) }
  exact ⟨next, nextResources, ⟨nextWitness⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
