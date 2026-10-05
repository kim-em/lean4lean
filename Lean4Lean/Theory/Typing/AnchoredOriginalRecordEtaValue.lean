import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionMixedRecord
import Lean4Lean.Theory.Typing.AnchoredLiteralRecordFields

/-! Record eta at the target endpoints is witnessed field by field by
primitive projection computation. Raw eta equality supplies typings and
projection origins; it is not used as a semantic equality principle. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles InductiveSignature
set_option backward.isDefEq.respectTransparency false

def etaConstructor (info : VProjectionInfo) (name : Name) (levels : List VLevel)
    (parameters : List VExpr) (major : VExpr) : VExpr :=
  mkApps (.const info.ctorName levels)
    (parameters ++ (List.range info.numFields).map fun index => .proj name index major)

private theorem liftApps (fn : VExpr) (args : List VExpr) (ρ : Lift) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact ih (.app fn arg)

theorem etaConstructor_lift (info : VProjectionInfo) (name : Name) (levels : List VLevel)
    (parameters : List VExpr) (major : VExpr) (ρ : Lift) :
    (etaConstructor info name levels parameters major).lift' ρ =
      etaConstructor info name levels (parameters.map (·.lift' ρ)) (major.lift' ρ) := by
  simp only [etaConstructor, liftApps, lift', List.map_append, List.map_map]
  rfl

theorem etaConstructor_subst (info : VProjectionInfo) (name : Name) (levels : List VLevel)
    (parameters : List VExpr) (major : VExpr) (σ : Subst) :
    (etaConstructor info name levels parameters major).subst σ =
      etaConstructor info name levels (parameters.map (·.subst σ)) (major.subst σ) := by
  simp only [etaConstructor, subst_mkApps, subst, List.map_append, List.map_map]
  rfl

private theorem projectionTrace
    (lookup : registry.projections name = some info)
    (selected : args[info.nparams + index]? = some field) :
    CanonicalDataHead.Trace registry
      (.proj name index (mkApps (.const info.ctorName levels) args)) [] field := by
  apply CanonicalDataHead.Trace.next (out := ⟨[], field⟩) _ .refl
  have projected : CanonicalDataHead.project registry name index
      (mkApps (.const info.ctorName levels) args) = some field := by
    simp only [CanonicalDataHead.project, lookup, bind, Option.bind_some,
      spine_mkApps_exact (.const info.ctorName levels) args rfl, ↓reduceIte, selected]
  simp only [CanonicalDataHead.step, CanonicalHead.step, getAppFnArgs, getAppFnArgs.go,
    CanonicalHead.spineStep, projected]

private theorem prepend
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (leftTrace : CanonicalDataHead.Trace registry left [] result)
    (rightTrace : CanonicalDataHead.Trace registry right [] result')
    (leftEq : env.IsDefEq U Γ left result domain)
    (rightEq : env.IsDefEq U Γ right result' domain)
    (related : Related env U registry Γ result result' domain input support) :
    Related env U registry Γ left right domain input support := by
  apply Related.prependEndpoints henv hscoped (.traced leftTrace) (.traced rightTrace)
    (show ProofInsertion env U Γ ([] ++ Γ) (.skipN .refl [].length) from .refl formed)
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using leftEq
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using rightEq
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl, Profile.rename_refl] using related

/-- The expanded left field computes to the original left projection.
The frozen field request, including its type support, is preserved. -/
theorem RequestAdmission.etaLeft
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {parameters : List VExpr}
    {left right type : VExpr} {index : Nat} {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (lookup : registry.projections name = some info)
    (parameterCount : parameters.length = info.nparams) (bound : index < info.numFields)
    (origin : ProjectionOrigin env U Γ info name index left type request.domain)
    (equal : env.IsDefEq U Γ (etaConstructor info name levels parameters left) left type)
    (admitted : RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index left) (.proj name index right)) :
    RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index (etaConstructor info name levels parameters left)) (.proj name index right) := by
  have selected : (parameters ++ (List.range info.numFields).map
      (fun j => VExpr.proj name j left))[info.nparams + index]? = some (.proj name index left) := by
    simp [← parameterCount, bound]
  have origin' := origin.replaceMajor equal.symm
  have fieldEq := IsDefEq.projIota origin.registered origin'.typed selected admitted.2.1.hasType.1
  have trace := projectionTrace (levels := levels) lookup selected
  refine ⟨admitted.1.trans fieldEq.symm, fieldEq.trans admitted.2.1,
    admitted.2.2.1, admitted.2.2.2.1, admitted.2.2.2.2.1, ?_, ?_⟩
  · exact prepend henv hscoped formed .refl trace
      admitted.1.hasType.1 fieldEq admitted.2.2.2.2.2.1
  · exact prepend henv hscoped formed trace .refl
      fieldEq admitted.2.1.hasType.2 admitted.2.2.2.2.2.2

def FieldRecordWitness.symm (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (witness : FieldRecordWitness env U registry lower Γ left right type name requests) :
    FieldRecordWitness env U registry lower Γ right left type name requests :=
  { witness with
    leftType := witness.rightType, rightType := witness.leftType
    leftOrigins := witness.rightOrigins, rightOrigins := witness.leftOrigins
    fields := witness.fields.symm laws hscoped }

/-- Expand one endpoint of the complete mixed field tuple. Each selected
field uses its original registered projection and an actual iota trace. -/
theorem FieldRecordWitness.etaLeft
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {parameters : List VExpr}
    {left right type : VExpr} {requests : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (registered : env.projections name info) (parameterCount : parameters.length = info.nparams)
    (equal : env.IsDefEq U Γ (etaConstructor info name levels parameters left) left type)
    (witness : FieldRecordWitness env U registry (relations env U registry n)
      Γ left right type name requests) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      (etaConstructor info name levels parameters left) right type name requests) := by
  obtain ⟨entry, member, _⟩ := witness.meaningful
  obtain ⟨origin⟩ := witness.leftOrigins entry member
  have sameInfo : info = witness.info := henv.projections_unique registered origin.registered
  subst info
  have moved := witness.insertion.eq henv equal
  have expanded : env.IsDefEq U witness.context
      (etaConstructor witness.info name levels (parameters.map (·.lift' witness.map)) (left.lift' witness.map))
      (left.lift' witness.map) (type.lift' witness.map) := by
    simpa only [etaConstructor_lift] using moved
  refine ⟨{ witness with leftType := moved.hasType.1, leftOrigins := ?_, fields := ?_ }⟩
  · intro entry member
    obtain ⟨origin⟩ := witness.leftOrigins entry member
    exact ⟨origin.replaceMajor moved.symm⟩
  · suffices ∀ selected : List (Nat × DataRequest (Profile n)), List.Subset selected requests →
        Arguments env U (relations env U registry n) witness.context
          (selected.map fun entry => entry.2.rename witness.map)
          (selected.map fun entry => .proj name entry.1
            ((etaConstructor witness.info name levels parameters left).lift' witness.map))
          (selected.map fun entry => .proj name entry.1 (right.lift' witness.map)) from
      this requests (fun _ member => member)
    intro selected
    induction selected with
    | nil => intro _; exact .nil
    | cons entry tail ih =>
      intro included
      have member := included List.mem_cons_self
      obtain ⟨origin⟩ := witness.leftOrigins entry member
      have admission := (witness.fields.map_member member).etaLeft henv hscoped
        (witness.insertion.targetWF henv witness.baseWF) witness.lookup
        (by simpa only [List.length_map] using parameterCount) (witness.bounded entry member)
        origin expanded
      exact .cons (by simpa only [etaConstructor_lift] using admission)
        (ih (fun _ present => included (List.mem_cons_of_mem _ present)))

private theorem equality (henv : env.Ordered) : LowerEquality env U registry (relations env U registry n) :=
  { code := fun route code => route.code henv code
    term := fun route term => route.term henv term
    retag := fun typed code term => Related.retag henv typed code term
    symm := fun term => Related.symm henv term
    trans := by
      intro hscoped Γ left middle right type value before after first second
      exact Related.trans henv hscoped first second }

theorem FieldRecordWitness.etaRight
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {parameters : List VExpr}
    {left right type : VExpr} {requests : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (registered : env.projections name info) (parameterCount : parameters.length = info.nparams)
    (equal : env.IsDefEq U Γ (etaConstructor info name levels parameters right) right type)
    (witness : FieldRecordWitness env U registry (relations env U registry n)
      Γ left right type name requests) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n) Γ
      left (etaConstructor info name levels parameters right) type name requests) := by
  obtain ⟨expanded⟩ := (witness.symm (equality henv) hscoped).etaLeft
    henv hscoped registered parameterCount equal
  exact ⟨expanded.symm (equality henv) hscoped⟩

/-- The fieldwise eta construction commutes with every future target world,
as required by the record relation rather than just one chosen witness. -/
theorem FieldRecordRelation.etaLeft
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {parameters : List VExpr}
    {left right type : VExpr} {requests : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (registered : env.projections name info) (parameterCount : parameters.length = info.nparams)
    (equal : env.IsDefEq U Γ (etaConstructor info name levels parameters left) left type)
    (relation : FieldRecordRelation env U registry (relations env U registry n)
      Γ left right type name requests) :
    FieldRecordRelation env U registry (relations env U registry n)
      Γ (etaConstructor info name levels parameters left) right type name requests := by
  intro Δ ρ future
  obtain ⟨witness⟩ := relation Δ ρ future
  have raw := equal.weak' henv future.weakening
  have expanded : env.IsDefEq U Δ
      (etaConstructor info name levels (parameters.map (·.lift' ρ)) (left.lift' ρ))
      (left.lift' ρ) (type.lift' ρ) := by simpa only [etaConstructor_lift] using raw
  simpa only [etaConstructor_lift] using witness.etaLeft henv hscoped registered
    (by simpa only [List.length_map] using parameterCount) expanded

theorem FieldRecordRelation.etaRight
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {parameters : List VExpr}
    {left right type : VExpr} {requests : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (registered : env.projections name info) (parameterCount : parameters.length = info.nparams)
    (equal : env.IsDefEq U Γ (etaConstructor info name levels parameters right) right type)
    (relation : FieldRecordRelation env U registry (relations env U registry n)
      Γ left right type name requests) :
    FieldRecordRelation env U registry (relations env U registry n)
      Γ left (etaConstructor info name levels parameters right) type name requests := by
  intro Δ ρ future
  obtain ⟨witness⟩ := relation Δ ρ future
  have raw := equal.weak' henv future.weakening
  have expanded : env.IsDefEq U Δ
      (etaConstructor info name levels (parameters.map (·.lift' ρ)) (right.lift' ρ))
      (right.lift' ρ) (type.lift' ρ) := by simpa only [etaConstructor_lift] using raw
  simpa only [etaConstructor_lift] using witness.etaRight henv hscoped registered
    (by simpa only [List.length_map] using parameterCount) expanded

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Once the actual constructor spine has yielded its finite mixed field
query, the original eta rule needs only its strictly earlier major F call.
Primitive projection computation then supplies the expanded target endpoint.
This is the value step, not the unproved constructor-spine source producer. -/
theorem MixedRecordQuery.etaValue
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {info : VProjectionInfo}
    {parameters : List VExpr} {levels : List VLevel} {expression : VExpr}
    {requests : List (Nat × DataRequest (Profile n))}
    (registered : sourceEnv.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation sourceEnv U source expression expression (mkApps (.const name levels) parameters))
    (constructor : Derivation sourceEnv U source
      (RankedData.etaConstructor info name levels parameters expression)
      (RankedData.etaConstructor info name levels parameters expression)
      (mkApps (.const name levels) parameters))
    (query : MixedRecordQuery env U registry target locals σ expression
      (mkApps (.const name levels) parameters) name requests footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamentals : FundamentalBelow sourceEnv env U registry (schedule .fundamental (Closure.close
      (Derivation.structEta registered parameterCount noIndices major constructor).origin context.closures).cost))
    (resources : footprint.Available available)
    (meaningful : ∃ entry ∈ requests, Profile.Nonempty entry.2.input) :
    ∃ nextFootprint,
      Nonempty (MixedRecordQuery env U registry target locals τ expression
        (mkApps (.const name levels) parameters) name requests nextFootprint) ∧
      nextFootprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n) target
        ((RankedData.etaConstructor info name levels parameters expression).subst σ)
        (expression.subst τ) ((mkApps (.const name levels) parameters).subst σ) name requests) := by
  have smaller : schedule .fundamental (Closure.close major.origin context.closures).cost <
      schedule .fundamental (Closure.close
        (Derivation.structEta registered parameterCount noIndices major constructor).origin context.closures).cost := by
    apply schedule_strict
    exact original_child_same_environment (Origin.rule_child (by simp)) context.closures
  obtain ⟨nextFootprint, next, nextResources, ⟨witness⟩⟩ := query.transfer major henv hscoped below
    closed formed context tails substitutions (fundamentals context major smaller) resources meaningful
  have original := (Derivation.structEta registered parameterCount noIndices major constructor).forget.defeq.mono below
  have raw := original.substDF henv substitutions.wf formed substitutions.left
  have equal : env.IsDefEq U target
      (RankedData.etaConstructor info name levels (parameters.map (·.subst σ)) (expression.subst σ))
      (expression.subst σ) ((mkApps (.const name levels) parameters).subst σ) := by
    simpa only [RankedData.etaConstructor, subst_mkApps, subst, List.map_append,
      List.map_map, Function.comp_def] using raw
  obtain ⟨expanded⟩ := witness.etaLeft henv hscoped (below.projections registered)
    (by simpa only [List.length_map] using parameterCount) equal
  exact ⟨nextFootprint, next, nextResources,
    ⟨by simpa only [RankedData.etaConstructor_subst] using expanded⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
