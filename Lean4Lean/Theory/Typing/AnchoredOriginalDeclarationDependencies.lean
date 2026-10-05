import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionCaptureBudget
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderCaptureMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterDependencies
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterRouteReserve

/-! Actual earlier-header dependency recursion. Each header is selected at
its actual universe instance, retaining its earlier original environment.
The recursion decreases finite constant-domain count at a header edge and
original proof size at ordinary child edges. No uniform universe-instance
bound or semantic theorem for an earlier header is assumed.
-/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

structure SelectedHeader (env : VEnv) (U : Nat) (expression : VExpr) where
  source : VEnv
  ordered : source.Ordered
  level : VLevel
  original : Derivation source U [] expression expression (.sort level)
  smaller : ∀ formed : env.Ordered, ordered.constantCount < formed.constantCount

noncomputable def selectOriginalHeader
    (formed : env.Ordered) (lookup : env.constants name = some value)
    (levelsWF : ∀ level ∈ levels, level.WF U) : SelectedHeader env U (value.type.instL levels) := by
  let origin := Classical.choice (formed.constantHeaderOrigin lookup)
  let typed := origin.typeInstance levelsWF
  let level := Classical.choose typed
  let original := Classical.choice (Derivation.reify (Classical.choose_spec typed))
  exact ⟨origin.source, origin.ordered, level, original, fun h => origin.count_lt h⟩

/-- The family header discovered in an actual major can differ from the
constructor header. Its weight is bounded by the retained owner roots, and
its complete parameter/index prefix receives a separate pre-answer reserve. -/
def projectionFamilyReserve (count field major : Nat) : Nat :=
  (field + major) * ((field + major + 2) ^ count * (1 + field + major))

theorem projectionFamilyReserve_mono (fieldBound : field ≤ field') (majorBound : major ≤ major') :
    projectionFamilyReserve count field major ≤ projectionFamilyReserve count field' major' := by
  apply Nat.mul_le_mul (Nat.add_le_add fieldBound majorBound)
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_left (show field + major + 2 ≤ field' + major' + 2 from by omega) count
  · omega

/-- The actual original projection index fixes the constructor prefix length.
No query-size or caller numerical reserve enters this expression. -/
def projectionDependencyReserve
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (_registered : env.projections name info) (index header field major : Nat) : Nat :=
  1 + field + major + header *
    ((header + 2) ^ (info.nparams + index) * (1 + field + major)) +
    projectionFamilyReserve (info.nparams + info.nindices) field major

/-- The retained simultaneous substitution has exactly the reserved number
of slots, including all earlier projections and no current projection. -/
theorem projection_capture_length
    {info : VProjectionInfo} {params : List VExpr}
    (parameterCount : params.length = info.nparams) (name : Lean.Name)
    (index : Nat) (major : VExpr) :
    (params ++ (List.range index).map (fun j => VExpr.proj name j major)).length =
      info.nparams + index := by
  simp only [List.length_append, List.length_map, List.length_range, parameterCount]

/-- This is a dependency-complete finite budget, not the final closure
schedule. Every original child and every actually selected constant or
projection constructor header contributes its recursively computed budget. -/
noncomputable def Derivation.declarationBudget
    (formed : env.Ordered) (original : Derivation env U source left right assigned) : Nat :=
  1 + original.origin.weight +
  match original with
  | .bvar _ _ formation => formation.declarationBudget formed
  | .symm original => original.declarationBudget formed
  | .trans first second => first.declarationBudget formed + second.declarationBudget formed
  | .sortDF .. => 0
  | .constDF (c := name) lookup levelsWF otherWF _ equivalent _ closed ambient =>
    let header := selectOriginalHeader formed lookup levelsWF
    let roots := constantParameterDependencies formed name levelsWF otherWF equivalent
    let parameters := (roots.map fun root => root.root.original.declarationBudget root.ordered).sum
    header.original.declarationBudget header.ordered + closed.declarationBudget formed + ambient.declarationBudget formed +
      parameterDependencyReserve roots.length 0 parameters 0 0
  | .elimDF _ _ _ _ _ _ _ formation => formation.declarationBudget formed
  | .appDF _ _ domain codomain function argument result =>
    domain.declarationBudget formed + codomain.declarationBudget formed + function.declarationBudget formed +
      argument.declarationBudget formed + result.declarationBudget formed
  | .projDF (info := info) (index := index) registered levelsWF _ _ _ _ _ field leftMajor rightMajor _ _ =>
    let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
    let roots := projectionParameterDependencies formed registered levelsWF
    let parameters := (roots.map fun root => root.root.original.declarationBudget root.ordered).sum
    projectionDependencyReserve registered index (header.original.declarationBudget header.ordered)
      (field.declarationBudget formed)
      (leftMajor.declarationBudget formed + rightMajor.declarationBudget formed) +
    parameterDependencyReserve (info.nparams + index) (header.original.declarationBudget header.ordered)
      parameters (field.declarationBudget formed)
      (leftMajor.declarationBudget formed + rightMajor.declarationBudget formed) +
    routedParameterDependencyReserve (info.nparams + max info.nindices index)
      (header.original.declarationBudget header.ordered) parameters (field.declarationBudget formed)
      (leftMajor.declarationBudget formed + rightMajor.declarationBudget formed)
  | .lamDF _ _ domain codomain codomain' body body' =>
    domain.declarationBudget formed + codomain.declarationBudget formed + codomain'.declarationBudget formed +
      body.declarationBudget formed + body'.declarationBudget formed
  | .forallEDF _ _ domain body body' =>
    domain.declarationBudget formed + body.declarationBudget formed + body'.declarationBudget formed
  | .defeqDF _ types terms => types.declarationBudget formed + terms.declarationBudget formed
  | .beta _ _ domain codomain body argument result instantiated =>
    domain.declarationBudget formed + codomain.declarationBudget formed + body.declarationBudget formed +
      argument.declarationBudget formed + result.declarationBudget formed + instantiated.declarationBudget formed
  | .eta _ _ domain codomain liftedCodomain term liftedTerm liftedDomain =>
    domain.declarationBudget formed + codomain.declarationBudget formed + liftedCodomain.declarationBudget formed +
      term.declarationBudget formed + liftedTerm.declarationBudget formed + liftedDomain.declarationBudget formed
  | .proofIrrel proposition left right =>
    proposition.declarationBudget formed + left.declarationBudget formed + right.declarationBudget formed
  | .extra _ _ _ _ formation left right ambientLeft ambientRight =>
    formation.declarationBudget formed + left.declarationBudget formed + right.declarationBudget formed +
      ambientLeft.declarationBudget formed + ambientRight.declarationBudget formed
  | .elimIota _ _ _ _ _ _ formation left right =>
    formation.declarationBudget formed + left.declarationBudget formed + right.declarationBudget formed
  | .projIota _ projection _ field => projection.declarationBudget formed + field.declarationBudget formed
  | .structEta _ _ _ major constructor => major.declarationBudget formed + constructor.declarationBudget formed
  | .unitLike _ _ _ _ left right => left.declarationBudget formed + right.declarationBudget formed
termination_by (formed.constantCount, sizeOf original)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ ((selectOriginalHeader _ _ _).smaller _)
    | exact Prod.Lex.left _ _ (SelectedParameterDependency.smaller _ _)
    | apply Prod.Lex.right; simp_wf; omega

theorem Derivation.origin_weight_lt_declarationBudget
    (formed : env.Ordered) (original : Derivation env U source left right assigned) :
    original.origin.weight < original.declarationBudget formed := by
  rw [declarationBudget.eq_def]
  omega

/-- The reserve of a projection already includes the full recursively
expanded earlier-header dependency budget at its exact universe instance. -/
theorem Derivation.projection_reserve_lt
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : Derivation env U source fieldType fieldType (.sort fieldLevel))
    (leftMajor : Derivation env U source sourceMajor major
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (rightMajor : Derivation env U source sourceMajor major'
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
    projectionDependencyReserve registered index (header.original.declarationBudget header.ordered)
      (field.declarationBudget formed)
      (leftMajor.declarationBudget formed + rightMajor.declarationBudget formed) <
    (Derivation.projDF registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field leftMajor rightMajor closed allowed).declarationBudget formed := by
  dsimp only
  rw [declarationBudget.eq_def formed (Derivation.projDF registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field leftMajor rightMajor closed allowed)]
  dsimp only
  omega

/-- A finite numerical reserve embedded in the existing origin algebra. -/
def reserveOrigin (reserve : Nat) : Origin := .rule (List.replicate reserve (.rule []))

theorem reserveOrigin_weight (reserve : Nat) : (reserveOrigin reserve).weight = 1 + reserve := by
  simp [reserveOrigin, Origin.weight]

def dependencyBetaLeftOrigin (domain codomain body argument result : Origin) : Origin :=
  capturedApplicationOrigin domain codomain (lambdaOrigin domain codomain body) argument result

def dependencyEtaBodyOrigin (codomain liftedCodomain liftedTerm liftedDomain : Origin) : Origin :=
  capturedApplicationOrigin liftedDomain liftedCodomain liftedTerm (.rule [liftedDomain]) codomain

def dependencyEtaLeftOrigin (domain codomain liftedCodomain liftedTerm liftedDomain : Origin) : Origin :=
  .binder domain [codomain, dependencyEtaBodyOrigin codomain liftedCodomain liftedTerm liftedDomain] []

/-- Production candidate: retain the existing binder/beta/eta products, but
recursively expand actual earlier headers and reserve projection captures.
This is isolated from `Derivation.origin` until located paths are ported. -/
noncomputable def Derivation.dependencyOrigin
    (formed : env.Ordered) (original : Derivation env U source left right type) : Origin :=
  match original with
  | .bvar _ _ formation => .rule [(formation.dependencyOrigin formed)]
  | .symm original => .rule [(original.dependencyOrigin formed)]
  | .trans first second => .rule [(first.dependencyOrigin formed), (second.dependencyOrigin formed)]
  | .sortDF .. => .rule []
  | .constDF (c := name) lookup levelsWF otherWF _ equivalent _ closed ambient =>
      let header := selectOriginalHeader formed lookup levelsWF
      let roots := constantParameterDependencies formed name levelsWF otherWF equivalent
      let parameters := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
      .rule [header.original.dependencyOrigin header.ordered,
        (closed.dependencyOrigin formed), (ambient.dependencyOrigin formed),
        reserveOrigin (parameterDependencyReserve roots.length 0 parameters 0 0)]
  | .elimDF _ _ _ _ _ _ _ formation => .rule [(formation.dependencyOrigin formed)]
  | .appDF _ _ domain codomain function argument result =>
      .rule [capturedApplicationOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (function.dependencyOrigin formed) (argument.dependencyOrigin formed) (result.dependencyOrigin formed),
        (result.dependencyOrigin formed)]
  | .projDF (info := info) (index := index) registered levelsWF _ _ _ _ _ field leftMajor rightMajor _ _ =>
      let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
      let roots := projectionParameterDependencies formed registered levelsWF
      let parameters := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
      let h := header.original.dependencyOrigin header.ordered
      let f := field.dependencyOrigin formed
      let l := leftMajor.dependencyOrigin formed
      let r := rightMajor.dependencyOrigin formed
      .rule [f, l, r, reserveOrigin (projectionDependencyReserve registered index h.weight f.weight
        (l.weight + r.weight) + parameterDependencyReserve (info.nparams + index) h.weight parameters
          f.weight (l.weight + r.weight) +
          routedParameterDependencyReserve (info.nparams + max info.nindices index)
            h.weight parameters f.weight (l.weight + r.weight))]
  | .lamDF _ _ domain codomain codomain' body body' =>
      .rule [lambdaOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (body.dependencyOrigin formed),
        lambdaOrigin (domain.dependencyOrigin formed) (codomain'.dependencyOrigin formed) (body'.dependencyOrigin formed),
        .binder (domain.dependencyOrigin formed) [(codomain'.dependencyOrigin formed), (codomain.dependencyOrigin formed)] []]
  | .forallEDF _ _ domain body body' => .binder (domain.dependencyOrigin formed) [(body.dependencyOrigin formed), (body'.dependencyOrigin formed)] []
  | .defeqDF _ types terms => .rule [(types.dependencyOrigin formed), (terms.dependencyOrigin formed)]
  | .beta _ _ domain codomain body argument result instantiated =>
      .rule [.typedBeta (domain.dependencyOrigin formed) (body.dependencyOrigin formed) (argument.dependencyOrigin formed) (instantiated.dependencyOrigin formed)
        [.binder (domain.dependencyOrigin formed) [(codomain.dependencyOrigin formed)] [], (result.dependencyOrigin formed)],
        dependencyBetaLeftOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (body.dependencyOrigin formed) (argument.dependencyOrigin formed) (result.dependencyOrigin formed)]
  | .eta _ _ domain codomain liftedCodomain term liftedTerm liftedDomain =>
      .rule [(term.dependencyOrigin formed),
        dependencyEtaLeftOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (liftedCodomain.dependencyOrigin formed) (liftedTerm.dependencyOrigin formed) (liftedDomain.dependencyOrigin formed)]
  | .proofIrrel proposition left right => .rule [(proposition.dependencyOrigin formed), (left.dependencyOrigin formed), (right.dependencyOrigin formed)]
  | .extra _ _ _ _ formation left right ambientLeft ambientRight =>
      .rule [(formation.dependencyOrigin formed), (left.dependencyOrigin formed), (right.dependencyOrigin formed), (ambientLeft.dependencyOrigin formed), (ambientRight.dependencyOrigin formed)]
  | .elimIota _ _ _ _ _ _ formation left right =>
      .rule [(formation.dependencyOrigin formed), (left.dependencyOrigin formed), (right.dependencyOrigin formed)]
  | .projIota _ projection _ field => .rule [(projection.dependencyOrigin formed), (field.dependencyOrigin formed)]
  | .structEta _ _ _ major constructor => .rule [(major.dependencyOrigin formed), (constructor.dependencyOrigin formed)]
  | .unitLike _ _ _ _ left right => .rule [(left.dependencyOrigin formed), (right.dependencyOrigin formed)]

termination_by (formed.constantCount, sizeOf original)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ ((selectOriginalHeader _ _ _).smaller _)
    | exact Prod.Lex.left _ _ (SelectedParameterDependency.smaller _ _)
    | apply Prod.Lex.right; simp_wf; omega

theorem Derivation.projection_dependencyOrigin_reserve_lt
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : Derivation env U source fieldType fieldType (.sort fieldLevel))
    (leftMajor : Derivation env U source sourceMajor major
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (rightMajor : Derivation env U source sourceMajor major'
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
    projectionDependencyReserve registered index ((header.original.dependencyOrigin header.ordered).weight)
      ((field.dependencyOrigin formed).weight)
      ((leftMajor.dependencyOrigin formed).weight + (rightMajor.dependencyOrigin formed).weight) <
    ((Derivation.projDF registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field leftMajor rightMajor closed allowed).dependencyOrigin formed).weight := by
  dsimp only
  rw [dependencyOrigin.eq_def formed (Derivation.projDF registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field leftMajor rightMajor closed allowed)]
  dsimp only
  simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    reserveOrigin_weight]
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
