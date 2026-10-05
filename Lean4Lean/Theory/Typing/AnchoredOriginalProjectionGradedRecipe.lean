import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionBinder
import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades

/-! A graded terminal capture keeps its original lower-grade frozen request.
The finite raw field query may have a larger grade. Only its admission is
adapted and lowered; the record descriptor and fixed support remain literal. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles AnchoredSource
open AnchoredSource.Adapted.OriginalFactorCut
open private chainRaise from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionInputMap
set_option backward.isDefEq.respectTransparency false

private theorem lowerTransport (henv : env.Ordered) :
    LowerTransport env U (relations env U registry n) :=
  ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩

theorem FieldRecordWitness.retagGraded
    {oldRequest : DataRequest (Profile M)} {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : FieldRecordWitness env U registry (relations env U registry M) Γ
      left right type name requests)
    (member : (index, oldRequest) ∈ requests) (bound : n ≤ M)
    (adapter : NormalProfileAdapter env U registry Γ oldRequest.input (raiseProfile M bound request.input))
    (alignment : DomainChain env U registry Γ request.input oldRequest.domain request.domain)
    (seed : RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index left))
    (meaningful : request.input.Nonempty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left right type name [(index, request)]) := by
  have highSeed := RequestAdmission.raiseFamily henv bound seed
  have highAlignment := chainRaise henv bound alignment
  have high : RequestAdmission env U (relations env U registry M) Γ
      (raiseDataRequest M bound request) (.proj name index left) (.proj name index right) :=
    RequestAdmission.retagField henv hscoped witness.baseWF adapter highAlignment highSeed
      (witness.admission henv hscoped member)
  have low := RequestAdmission.lowerFamily henv bound witness.baseWF high
  have joined := admission_transport henv (lowerTransport henv) witness.insertion low
  have path := witness.insertion.path henv alignment.path
  refine ⟨{
    meaningful := ⟨(index, request), List.mem_singleton_self _, meaningful⟩
    baseWF := witness.baseWF, context := witness.context, map := witness.map
    insertion := witness.insertion, info := witness.info, lookup := witness.lookup
    ctorDefinition := witness.ctorDefinition, ctorNative := witness.ctorNative
    ctorQuotient := witness.ctorQuotient, leftType := witness.leftType, rightType := witness.rightType
    bounded := ?_, leftOrigins := ?_, rightOrigins := ?_, fields := .cons joined .nil }⟩
  · intro entry present
    cases List.mem_singleton.mp present
    exact witness.bounded (index, oldRequest) member
  · intro entry present
    cases List.mem_singleton.mp present
    obtain ⟨origin⟩ := witness.leftOrigins _ member
    exact ⟨{ origin with fieldPath := origin.fieldPath.trans path }⟩
  · intro entry present
    cases List.mem_singleton.mp present
    obtain ⟨origin⟩ := witness.rightOrigins _ member
    exact ⟨{ origin with fieldPath := origin.fieldPath.trans path }⟩

end Lean4Lean.AnchoredSemantics.RankedData
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor
open private raiseProfile_map_atoms from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionInputMap
set_option backward.isDefEq.respectTransparency false

structure GradedFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) where
  rank : Nat
  bound : n ≤ rank
  rawRequest : DataRequest (Profile rank)
  raw : WholeFieldRecipe env U registry target locals σ major name index rawRequest
  adapter : NormalProfileAdapter env U registry target rawRequest.input (raiseProfile rank bound request.input)
  alignment : DomainChain env U registry target request.input rawRequest.domain request.domain
  seed : RankedData.RequestAdmission env U (relations env U registry n) target request
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  meaningful : request.input.Nonempty

noncomputable def AdaptedFieldRecipe.graded
    (query : AdaptedFieldRecipe env U registry target locals σ major name index request) :
    GradedFieldRecipe env U registry target locals σ major name index request := {
  rank := _, bound := Nat.le_refl _, rawRequest := query.rawRequest, raw := query.raw
  adapter := by simpa only [raiseProfile_self] using query.adapter
  alignment := query.alignment, seed := query.seed, meaningful := query.meaningful }

theorem ProjectionSeededFrame.gradedRecipe
    {node : EndpointState sourceEnv U source (.proj name index major) A}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProjectionSeededFrame env registry target node locals σ available B result)
    (request : DataRequest (Profile n)) (bound : n ≤ frame.collected.rank)
    (adapter : NormalProfileAdapter env U registry target frame.input
      (raiseProfile frame.collected.rank bound request.input))
    (alignment : DomainChain env U registry target request.input (A.subst σ) request.domain)
    (seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (meaningful : request.input.Nonempty) :
    ∃ query : GradedFieldRecipe env U registry target locals σ major name index request,
      query.raw.footprint.Available available := by
  have high : (raiseProfile frame.collected.rank bound request.input).Nonempty := by
    change raiseProfile frame.collected.rank bound request.input ≠ []
    rw [raiseProfile_map_atoms]
    exact fun empty => meaningful (List.map_eq_nil_iff.mp empty)
  obtain ⟨raw, resources⟩ := frame.wholeRecipe henv hscoped (normalAdapter_nonempty adapter high)
  exact ⟨⟨frame.collected.rank, bound, ⟨frame.key, frame.support⟩, raw, adapter, alignment, seed, meaningful⟩,
    resources⟩

/-- A reified terminal capture constructs its field recipe at the exact
original request grade. The raw projected query is interpreted only at its
actual original endpoint; its assigned type is never changed syntactically. -/
theorem ProjectionGradedResult.fieldRecipe
    {node : EndpointState sourceEnv U source (.proj name index major) A}
    {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry (projectionHead node).route initial)
    (fieldFundamental : StateFundamental env registry initial (projectionHead node).field)
    (majorFundamental : DerivationFundamental env registry initial (projectionHead node).major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (value : ProjectionGradedResult env registry target node locals σ available request.input)
    (alignment : DomainChain env U registry target request.input (A.subst σ) request.domain)
    (seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (meaningful : request.input.Nonempty) :
    ∃ query : GradedFieldRecipe env U registry target locals σ major name index request,
      query.raw.footprint.Available available := by
  obtain ⟨answer⟩ := value.query.diagonalAt (projectionHead node) henv hscoped below initial
    calls fieldFundamental majorFundamental closed formed substitutions tails value.resources
  have raw : env.HasType U target ((VExpr.proj name index major).subst σ) (A.subst σ) :=
    (node.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  let argument : ProjectionArgumentSeed env registry target node locals σ available :=
    ⟨value.rank, value.raw, value.footprint, value.query, value.resources⟩
  let collected : ProjectionFactoredArguments env registry target node locals σ available
      [] [] (max 0 argument.rank) := {
    rank := value.rank, bound := by simp [argument], input := .empty, footprint := []
    query := .empty, resources := (fun _ _ member => nomatch member), pack := .nil }
  let frame : ProjectionSeededFrame env registry target node locals σ available (.bvar 0) (.empty : Profile 0) := {
    seed := argument, required := [], outside := [], collected := collected
    outsideResources := fun _ _ member => nomatch member
    support := answer.support, domainFootprint := answer.footprint, domain := answer.certificate
    domainResources := answer.resources
    guard := by
      change LambdaGuard env U registry target σ A
        ⟨A.subst σ, (VExpr.proj name index major).subst σ,
          (raiseProfile value.rank (Nat.le_refl _) value.raw).union .empty⟩ answer.support
      simp only [raiseProfile_self, Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil]
      exact ⟨answer.typed, answer.certificate.formed, .refl, answer.code,
        ⟨raw, raw, _, answer.typed, answer.certificate.formed, answer.code,
          answer.related, answer.related⟩⟩
    body := by
      rw [raiseProfile_empty]
      exact .seed .empty (.empty (.sort true)) }
  have adapter : NormalProfileAdapter env U registry target frame.input
      (raiseProfile frame.collected.rank value.bound request.input) := by
    change NormalProfileAdapter env U registry target
      ((raiseProfile value.rank (Nat.le_refl _) value.raw).union .empty)
      (raiseProfile value.rank value.bound request.input)
    simpa only [raiseProfile_self, Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using value.adapter
  exact frame.gradedRecipe henv hscoped request value.bound adapter alignment seed meaningful

theorem GradedFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {request : DataRequest (Profile n)}
    {left right type : VExpr}
    (query : GradedFieldRecipe env U registry target locals σ left name index request)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : query.raw.footprint.Available available) :
    ∃ next : GradedFieldRecipe env U registry target locals τ right name index request,
      next.raw.footprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name [(index, request)]) := by
  obtain ⟨raw, nextResources, ⟨witness⟩⟩ := query.raw.transfer original henv hscoped
    closed formed context tails substitutions fundamental resources
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj name index (left.subst σ)) (.proj name index (left.subst σ)) := by
    simpa only [subst] using query.seed
  obtain ⟨nextWitness⟩ := witness.retagGraded henv hscoped (List.mem_singleton_self _) query.bound
    query.adapter query.alignment seed query.meaningful
  obtain ⟨anchor, pair, typed, supportFormed, code, first, last⟩ :=
    nextWitness.admission henv hscoped (List.mem_singleton_self _)
  let next : GradedFieldRecipe env U registry target locals τ right name index request := {
    rank := query.rank, bound := query.bound, rawRequest := query.rawRequest, raw := raw
    adapter := query.adapter, alignment := query.alignment, meaningful := query.meaningful
    seed := by
      simpa only [subst] using
        (show RankedData.RequestAdmission env U (relations env U registry n) target request
          (.proj name index (right.subst τ)) (.proj name index (right.subst τ)) from
          ⟨anchor.trans pair, pair.hasType.2, typed, supportFormed, code,
            Related.trans henv hscoped first last,
            Related.trans henv hscoped (Related.symm henv last) last⟩) }
  exact ⟨next, nextResources, ⟨nextWitness⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
