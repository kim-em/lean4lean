import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix

/-! Traversal of actual semantic source frames, including the field metadata
and major query of nested projections. All children retain the original path
and exact context derivation; no source query is reflected out of a binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The output support of owner F remains inside that same original source
tree, at its computed assigned formation. The semantic source frame is exact. -/
noncomputable def OriginalRichOccurrenceFrame.assignedFormation
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame (.assignedFormation location) initialContext env registry target locals σ τ available
      ordered initialEnvironment :=
  ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.PrefixRoute.locate_dependencyEnvironment
    (route : PrefixRoute sourceEnv U source expression first last) (start : Located root first)
    (ordered : sourceEnv.Ordered) (initial : List Closure) :
    (route.locate start).dependencyEnvironment ordered initial = start.dependencyEnvironment ordered initial := by
  induction route with
  | done => rfl
  | expose reference rest ih => exact ih (.expose start)
  | convert plan term rest ih => exact ih (.convertTerm start)

noncomputable def OriginalRichOccurrenceFrame.route
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U occurrenceSource expression assigned}
    {last : EndpointState sourceEnv U occurrenceSource expression natural}
    {location : Located root first}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (route : PrefixRoute sourceEnv U occurrenceSource expression first last) :
    OriginalRichOccurrenceFrame (route.locate location) initialContext env registry target locals σ τ available
      ordered initialEnvironment := by
  induction route with
  | done => exact occurrence
  | expose reference rest ih =>
      exact ih ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩
  | convert plan term rest ih =>
      exact ih ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.projField
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index major) assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (head : ProjectionHead node) :
    OriginalRichOccurrenceFrame (.projField (head.route.locate location)) initialContext
      env registry target locals σ τ available ordered initialEnvironment := by
  let natural := occurrence.route head.route
  exact ⟨natural.frame, natural.substitutions, natural.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.projMajor
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index major) assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (head : ProjectionHead node) :
    OriginalRichOccurrenceFrame (.projMajor (head.route.locate location)) initialContext
      env registry target locals σ τ available ordered initialEnvironment := by
  let natural := occurrence.route head.route
  exact ⟨natural.frame, natural.substitutions, natural.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.piDomain
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame (.piDomain location) initialContext env registry target locals σ τ available
      ordered initialEnvironment :=
  ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.lamDomain
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame (.lamDomain location) initialContext env registry target locals σ τ available
      ordered initialEnvironment :=
  ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.lamBody
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target
      (.ref (Classical.choose location.originalDomains.1)) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (raw : env.IsDefEq U target x y (A.subst σ))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    OriginalRichOccurrenceFrame (.lamBody location) initialContext env registry target (Locals.push locals)
      (σ.cons x) (τ.cons y) (available.push needs) ordered initialEnvironment := by
  let original := Classical.choose location.originalDomains.1
  have same : domain = .ref original := Classical.choose_spec location.originalDomains.1
  refine {
    frame := .bind occurrence.frame original certificate resources typed arguments needs bounded covered
    substitutions := .cons occurrence.substitutions (original.sound.defeq.mono sourceBelow) raw
    environment_le := ?_ }
  have previous := occurrence.environment_le
  change max ((original.dependencyOrigin ordered).weight *
      (1 + environmentCost (occurrence.frame.dependencyEnvironment ordered)))
      (environmentCost (occurrence.frame.dependencyEnvironment ordered)) ≤
    max ((domain.dependencyOrigin ordered).weight *
      (1 + environmentCost (location.dependencyEnvironment ordered initialEnvironment)))
      (environmentCost (location.dependencyEnvironment ordered initialEnvironment))
  have weightEq := congrArg (fun node => (node.dependencyOrigin ordered).weight) same
  rw [weightEq]
  exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left previous _)) (Nat.le_max_left _ _),
    Nat.le_trans previous (Nat.le_max_right _ _)⟩

private theorem guardArguments (henv : env.Ordered)
    (guard : LambdaGuard env U registry target σ A key ambient) :
    Related env U registry target key.anchor key.anchor (A.subst σ) key.input ambient := by
  obtain ⟨_, _, _, _, _, _, _, arguments⟩ := guard.anchor
  exact Related.convert henv guard.inputTyped guard.domains arguments

noncomputable def OriginalRichOccurrenceFrame.piAnchor
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    OriginalRichOccurrenceFrame (.piBody location) initialContext env registry target (Locals.push locals)
      (σ.cons key.anchor) (τ.cons key.anchor)
      (available.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons))
      ordered initialEnvironment := by
  have same := Classical.choose_spec location.originalDomains.1
  exact occurrence.piBody sourceBelow (same ▸ certificate) resources guard.inputTyped
    (guardArguments henv guard) (guard.path.cast guard.anchor.1) _
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom atomMember => covered atom ((pack.atomized_localNeeds need member).2 atom atomMember))

noncomputable def OriginalRichOccurrenceFrame.lamAnchor
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    OriginalRichOccurrenceFrame (.lamBody location) initialContext env registry target (Locals.push locals)
      (σ.cons key.anchor) (τ.cons key.anchor)
      (available.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons))
      ordered initialEnvironment := by
  have same := Classical.choose_spec location.originalDomains.1
  exact occurrence.lamBody sourceBelow (same ▸ certificate) resources guard.inputTyped
    (guardArguments henv guard) (guard.path.cast guard.anchor.1) _
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom atomMember => covered atom ((pack.atomized_localNeeds need member).2 atom atomMember))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
