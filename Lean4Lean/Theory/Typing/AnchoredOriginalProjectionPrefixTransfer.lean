import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionObserverReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalTailPrefix

/-! Typed projection queries pass through their actual original conversion
prefixes. The finite field certificate is replayed at its exact support and
the domain chain is extended by that same answer. This lets constructor/eta
argument queries retain their original inferred types instead of requiring
that they were already primitive projection heads.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

namespace OriginalProjectionMetadata

/-- Reindex one field packet without changing its source major request. -/
noncomputable def changeType
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {first : EndpointState sourceEnv U source (.proj name index major) A}
    (last : EndpointState sourceEnv U source (.proj name index major) B)
    (query : OriginalProjectionMetadata env registry target first locals σ demand request)
    (types : CodeTransferResult env U registry target locals σ σ available A B query.packet.support)
    (path : TypeConversion env U target (A.subst σ) (B.subst σ)) :
    OriginalProjectionMetadata env registry target last locals σ demand request := {
  name_eq := query.name_eq
  packet := {
    member := query.packet.member
    majorFootprint := query.packet.majorFootprint
    majorObservation := query.packet.majorObservation
    support := query.packet.support
    fieldFootprint := types.footprint
    fieldCertificate := types.certificate
    typed := query.packet.typed
    alignment := query.packet.alignment.trans (.step path query.packet.typed
      query.packet.fieldCertificate.formed types.related (.refl _)) } }

/-- Every semantic call belongs to an actual conversion child in `route`.
The terminal projection rule is not interpreted by this operation. -/
theorem replayPrefix
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation}
    {first : EndpointState sourceEnv U source (.proj name index major) assigned}
    {last : EndpointState sourceEnv U source (.proj name index major) natural}
    (route : PrefixRoute sourceEnv U source (.proj name index major) first last)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry route initial)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target first locals σ demand request)
    (majorResources : query.packet.majorFootprint.Available available)
    (fieldResources : query.packet.fieldFootprint.Available available) :
    ∃ next : OriginalProjectionMetadata env registry target last locals σ demand request,
      next.packet.support = query.packet.support ∧
      next.packet.majorFootprint.Available available ∧
      next.packet.fieldFootprint.Available available := by
  induction route with
  | done => exact ⟨query, rfl, majorResources, fieldResources⟩
  | expose reference rest ih =>
    exact ih (fun call => calls (.expose call))
      ⟨query.packet, query.name_eq⟩ majorResources fieldResources
  | convert plan term rest ih =>
    obtain ⟨level, backwards, _⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed formed substitutions tails
    obtain ⟨types⟩ := query.packet.fieldCertificate.transfer_graded henv hscoped formed
      closed backwards fieldResources
    obtain ⟨rawLevel, _, raw⟩ := plan.sound
    have path : TypeConversion env U target _ _ := .single
      ((raw.symm.defeq.mono below).substDF henv substitutions.wf formed substitutions)
    exact ih (fun call => calls (.tail call)) (changeType term query types path)
      majorResources types.available

/-- Restore the original assigned type after a primitive projection query
has been interpreted. This is a construction from original prefix children,
not a caller-supplied alignment of the outgoing field. -/
theorem restorePrefix
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation}
    {first : EndpointState sourceEnv U source (.proj name index major) assigned}
    {last : EndpointState sourceEnv U source (.proj name index major) natural}
    (route : PrefixRoute sourceEnv U source (.proj name index major) first last)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry route initial)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target last locals σ demand request)
    (majorResources : query.packet.majorFootprint.Available available)
    (fieldResources : query.packet.fieldFootprint.Available available) :
    ∃ next : OriginalProjectionMetadata env registry target first locals σ demand request,
      next.packet.support = query.packet.support ∧
      next.packet.majorFootprint.Available available ∧
      next.packet.fieldFootprint.Available available := by
  induction route with
  | done => exact ⟨query, rfl, majorResources, fieldResources⟩
  | expose reference rest ih =>
    obtain ⟨next, same, nextMajor, nextField⟩ := ih (fun call => calls (.expose call)) query majorResources fieldResources
    exact ⟨⟨next.packet, next.name_eq⟩, same, nextMajor, nextField⟩
  | convert plan term rest ih =>
    obtain ⟨inner, same, innerMajor, innerField⟩ := ih (fun call => calls (.tail call)) query majorResources fieldResources
    obtain ⟨level, _, forward⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed formed substitutions tails
    obtain ⟨types⟩ := inner.packet.fieldCertificate.transfer_graded henv hscoped formed
      closed forward innerField
    obtain ⟨rawLevel, _, raw⟩ := plan.sound
    have path : TypeConversion env U target _ _ := .single
      ((raw.defeq.mono below).substDF henv substitutions.wf formed substitutions)
    exact ⟨changeType (.convert plan term) inner types path, same, innerMajor, types.available⟩

end OriginalProjectionMetadata

/-- Lift an exact per-field reconstruction through the entire typed query
syntax. The output keeps each original requested atom, including downward
grade changes; empty queries require no field witness. -/
theorem ProjectionObs.mapFields
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation}
    {first : EndpointState sourceEnv U source (.proj name index major) assigned}
    {last : EndpointState sourceEnv U source (.proj name index major) natural}
    (query : ProjectionObs env registry target first locals σ demand footprint)
    (fields : ∀ {n : Nat} {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (field : OriginalProjectionMetadata env registry target first locals σ record request),
      field.packet.majorFootprint.Available available →
      field.packet.fieldFootprint.Available available →
      ∃ next : OriginalProjectionMetadata env registry target last locals σ record request,
        next.packet.support = field.packet.support ∧
        next.packet.majorFootprint.Available available ∧
        next.packet.fieldFootprint.Available available)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target last locals σ demand nextFootprint) ∧
      nextFootprint.Available available := by
  induction query with
  | field nameEq member majorObservation fieldCertificate typed alignment =>
    let metadata : OriginalProjectionMetadata env registry target first locals σ _ _ :=
      ⟨⟨member, _, majorObservation, _, _, fieldCertificate, typed, alignment⟩, nameEq⟩
    obtain ⟨next, _, nextMajor, nextField⟩ := fields metadata
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨next.packet.majorFootprint ++ next.packet.fieldFootprint,
      ⟨.field next.name_eq next.packet.member next.packet.majorObservation
        next.packet.fieldCertificate next.packet.typed next.packet.alignment⟩,
      fun i need member => (List.mem_append.mp member).elim (nextMajor i need) (nextField i need)⟩
  | empty => exact ⟨[], ⟨.empty⟩, fun _ _ member => nomatch member⟩
  | union left right ihLeft ihRight =>
    obtain ⟨leftFootprint, ⟨leftQuery⟩, leftResources⟩ :=
      ihLeft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨rightFootprint, ⟨rightQuery⟩, rightResources⟩ :=
      ihRight (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨leftFootprint ++ rightFootprint, ⟨.union leftQuery rightQuery⟩,
      fun i need member => (List.mem_append.mp member).elim
        (leftResources i need) (rightResources i need)⟩
  | view child change ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.view next change⟩, nextResources⟩
  | raise child bound ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.raise next bound⟩, nextResources⟩
  | unpad child ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.unpad next⟩, nextResources⟩

/-- Full typed query replay at an arbitrary original projection occurrence. -/
theorem ProjectionObs.replayPrefix
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation}
    {first : EndpointState sourceEnv U source (.proj name index major) assigned}
    {last : EndpointState sourceEnv U source (.proj name index major) natural}
    (query : ProjectionObs env registry target first locals σ demand footprint)
    (route : PrefixRoute sourceEnv U source (.proj name index major) first last)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry route initial)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target last locals σ demand nextFootprint) ∧
      nextFootprint.Available available :=
  query.mapFields (fun field majorResources fieldResources =>
    OriginalProjectionMetadata.replayPrefix route henv hscoped below initial calls closed formed
      substitutions tails field majorResources fieldResources) resources

/-- Restore every field's actual original assigned type, including wrappers
whose constituent queries were created at different grades. -/
theorem ProjectionObs.restorePrefix
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation}
    {first : EndpointState sourceEnv U source (.proj name index major) assigned}
    {last : EndpointState sourceEnv U source (.proj name index major) natural}
    (query : ProjectionObs env registry target last locals σ demand footprint)
    (route : PrefixRoute sourceEnv U source (.proj name index major) first last)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry route initial)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target first locals σ demand nextFootprint) ∧
      nextFootprint.Available available :=
  query.mapFields (fun field majorResources fieldResources =>
    OriginalProjectionMetadata.restorePrefix route henv hscoped below initial calls closed formed
      substitutions tails field majorResources fieldResources) resources

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
