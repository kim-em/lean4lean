import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameRaw

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RawRichGroupEntries.ownerClosures
    {sourceEnv : VEnv} {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (ordered : sourceEnv.Ordered) (declared : Closure)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : List Closure :=
  match entries with
  | .nil => []
  | .cons entry tail => .bundle (entry.owner.dependencyClosure ordered ownerInitial) declared ::
      tail.ownerClosures ordered declared

noncomputable def RawOriginalRichFrame.dependencyEnvironment {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} (ordered : sourceEnv.Ordered)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : List Closure :=
  match frame with
  | .reserve frame closures => closures ++ frame.dependencyEnvironment ordered
  | .merge left right => left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered
  | .nil => []
  | .header capturedOrdered initial frame => frame.dependencyEnvironment ordered capturedOrdered initial
  | .bind tail domain .. =>
      .close (domain.dependencyOrigin ordered) (tail.dependencyEnvironment ordered) :: tail.dependencyEnvironment ordered
  | .capture tail domain _ argument .. =>
      let previous := tail.dependencyEnvironment ordered
      .bundle (.close (argument.dependencyOrigin ordered) previous)
        (.close (domain.dependencyOrigin ordered) previous) :: previous
  | .group (field := field) (major := major) tail domain capturedOrdered ownerInitial entries =>
      let previous := tail.dependencyEnvironment ordered
      let declared := Closure.close (domain.dependencyOrigin ordered) previous
      declared ::
        Closure.bundle (.close (field.dependencyOrigin capturedOrdered) ownerInitial) declared ::
        Closure.bundle (.close (major.dependencyOrigin capturedOrdered) ownerInitial) declared ::
        entries.ownerClosures capturedOrdered declared ++ previous

private theorem RawRichGroupEntry.frame_size_lt
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    sizeOf entry.frame < sizeOf entry := by
  cases entry
  simp [RawRichGroupEntry.frame]
  omega

mutual
noncomputable def RawOriginalRichFrame.Valid
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match frame with
  | .reserve frame _ => frame.Valid
  | .merge left right => left.Valid ∧ right.Valid
  | .nil | .header .. => True
  | .bind tail .. | .capture tail .. => tail.Valid
  | .group tail _ _ _ entries => tail.Valid ∧ entries.Valid
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.Valid
    {sourceEnv : VEnv} {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Prop :=
  match entries with
  | .nil => True
  | .cons entry tail => entry.frame.Valid ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (entry.frame.dependencyEnvironment ordered) ≤
          environmentCost (entry.owner.dependencyEnvironment ordered ownerInitial)) ∧ tail.Valid
termination_by sizeOf entries
decreasing_by
  all_goals simp_wf
  · have bound := RawRichGroupEntry.frame_size_lt entry
    omega
  · omega
end

/-- Public frames carry validity of every retained heterogeneous owner frame.
The measured environment is computed from the raw original tree. -/
structure OriginalRichFrame (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) where
  raw : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available
  valid : raw.Valid

noncomputable def OriginalRichFrame.dependencyEnvironment {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) : List Closure :=
  frame.raw.dependencyEnvironment ordered

/-- Merge keeps both original frame derivations. Resource lookup selects the
branch that supplied the requested need; no owner lineage is discarded. -/
noncomputable def OriginalRichFrame.merge
    {context : ContextDerivation sourceEnv U source}
    (left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
    (right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
    OriginalRichFrame sourceEnv env U registry target context locals σ τ
      (leftAvailable.append rightAvailable) :=
  ⟨.merge left.raw right.raw, by
    simpa only [RawOriginalRichFrame.Valid] using And.intro left.valid right.valid⟩

theorem OriginalRichFrame.merge_environment
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
    (right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
    (left.merge right).dependencyEnvironment ordered =
      left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered := rfl

theorem merge_environmentCost_append (left right : List Closure) :
    environmentCost (left ++ right) = max (environmentCost left) (environmentCost right) := by
  induction left with
  | nil => simp [environmentCost]
  | cons head tail ih =>
    simp only [List.cons_append, environmentCost, ih, Nat.max_assoc]

/-- Merging independently constructed queries costs the maximum of their
actual environments, never the sum of query multiplicities. -/
theorem OriginalRichFrame.merge_environmentCost
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
    (right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
    environmentCost ((left.merge right).dependencyEnvironment ordered) =
      max (environmentCost (left.dependencyEnvironment ordered))
        (environmentCost (right.dependencyEnvironment ordered)) :=
  merge_environmentCost_append _ _

/-- A retained finite history is charged outside the head slot. It changes
neither semantic resources nor the source context. Operative generation
restricts this raw wrapper to a concrete original history. -/
noncomputable def OriginalRichFrame.reserve
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closures : List Closure) :
    OriginalRichFrame sourceEnv env U registry target context locals σ τ available :=
  ⟨.reserve frame.raw closures, by simpa only [RawOriginalRichFrame.Valid] using frame.valid⟩

theorem OriginalRichFrame.reserve_environment
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closures : List Closure) :
    (frame.reserve closures).dependencyEnvironment ordered =
      closures ++ frame.dependencyEnvironment ordered := rfl

theorem OriginalRichFrame.reserve_environmentCost
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closures : List Closure) :
    environmentCost ((frame.reserve closures).dependencyEnvironment ordered) =
      max (environmentCost closures) (environmentCost (frame.dependencyEnvironment ordered)) :=
  merge_environmentCost_append _ _

def OriginalRichFrame.nil : OriginalRichFrame sourceEnv env U registry target .nil locals σ τ available :=
  ⟨.nil, by simp [RawOriginalRichFrame.Valid]⟩

noncomputable def OriginalRichFrame.header
    {header : EndpointRef sourceEnv U [] headerExpression headerType}
    {field : EndpointRef capturedEnv U capturedSource fieldExpression fieldType}
    {major : EndpointRef capturedEnv U capturedSource majorExpression majorType}
    (capturedOrdered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry target context locals σ τ available :=
  ⟨.header capturedOrdered initial frame, by simp [RawOriginalRichFrame.Valid]⟩

noncomputable def OriginalRichFrame.bind
    {context : ContextDerivation sourceEnv U source}
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    OriginalRichFrame sourceEnv env U registry target (.cons context domain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (available.push needs) :=
  ⟨.bind tail.raw domain certificate resources typed arguments needs bounded covered, by simpa only [RawOriginalRichFrame.Valid] using tail.valid⟩


noncomputable def OriginalRichFrame.capture
    {context : ContextDerivation sourceEnv U source}
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (argumentLocation : Located root argument)
    (argumentLineage : argumentLocation.contextDerivation initialContext = context)
    (argumentQuery : RichObs sourceEnv env U registry target argument locals σ
      (rawInput : Profile k) argumentFootprint)
    (argumentAvailable : argumentFootprint.Available available)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    OriginalRichFrame sourceEnv env U registry target (.cons context domain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (available.push needs) :=
  ⟨.capture tail.raw domain initialContext argument argumentLocation argumentLineage
    argumentQuery argumentAvailable certificate resources typed arguments needs bounded covered,
    by simpa only [RawOriginalRichFrame.Valid] using tail.valid⟩


structure RichGroupedCaptureEntry
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (ownerInitial : List Closure) (rawCapture leftValue rightValue : VExpr) where
  owner : HeaderOwner field major
  ownerLocals : List Nat
  ownerLeft : Subst
  ownerRight : Subst
  ownerAvailable : Valuation
  initialContext : ContextDerivation sourceEnv U source
  frame : OriginalRichFrame sourceEnv env U registry target
    (owner.context initialContext) ownerLocals ownerLeft ownerRight ownerAvailable
  substitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source
  frame_environment_le : ∀ ordered : sourceEnv.Ordered,
    environmentCost (frame.dependencyEnvironment ordered) ≤
      environmentCost (owner.dependencyEnvironment ordered ownerInitial)
  depth : Nat
  sourcePrefix : List VExpr
  source_eq : owner.source = sourcePrefix ++ source
  depth_eq : depth = sourcePrefix.length
  expression_eq : owner.expression = rawCapture.lift' (.skipN .refl depth)
  left_eq : owner.expression.subst ownerLeft = leftValue
  right_eq : owner.expression.subst ownerRight = rightValue
  rank : Nat
  input : Profile rank
  queryRank : Nat
  queryInput : Profile queryRank
  queryBound : rank ≤ queryRank
  queryAdapter : GeneralNormalProfileAdapter env U registry target queryInput
    (raiseProfile queryRank queryBound input)
  footprint : Footprint
  query : RichObs sourceEnv env U registry target owner.node ownerLocals ownerLeft queryInput footprint
  queryAvailable : footprint.Available ownerAvailable
  answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
    ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input


variable {sourceEnv headerEnv env : VEnv} {U : Nat} {source headerSource target : List VExpr}
variable {fieldExpression fieldType majorExpression majorType A : VExpr} {level : VLevel}
variable {field : EndpointRef sourceEnv U source fieldExpression fieldType}
variable {major : EndpointRef sourceEnv U source majorExpression majorType}
variable {domain : EndpointRef headerEnv U headerSource A (.sort level)}
variable {registry : CanonicalHead.Registry} {headerLocals : List Nat} {declaredLeft : Subst}
variable {headerAvailable : Valuation} {ownerInitial : List Closure} {rawCapture leftValue rightValue : VExpr}

noncomputable def RichGroupedCaptureEntry.toRaw
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue entry.rank entry.input :=
  .mk entry.owner entry.ownerLocals entry.ownerLeft entry.ownerRight entry.ownerAvailable entry.initialContext
    entry.frame.raw entry.substitutions entry.depth entry.sourcePrefix entry.source_eq entry.depth_eq
    entry.expression_eq entry.left_eq entry.right_eq entry.queryRank entry.queryInput entry.queryBound entry.queryAdapter entry.footprint entry.query entry.queryAvailable entry.answer

noncomputable def richGroupedEntriesRaw
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)) :
    RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue
      (entries.flatMap (fun entry => captureNeeds entry.input)) :=
  match entries with
  | [] => .nil
  | entry :: tail => .cons entry.toRaw (richGroupedEntriesRaw tail)

theorem richGroupedEntriesRaw_valid
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)) :
    (richGroupedEntriesRaw entries).Valid := by
  induction entries with
  | nil => simp [richGroupedEntriesRaw, RawRichGroupEntries.Valid]
  | cons entry tail ih =>
    simpa only [richGroupedEntriesRaw, RawRichGroupEntries.Valid, RichGroupedCaptureEntry.toRaw,
      RawRichGroupEntry.frame, RawRichGroupEntry.owner, OriginalRichFrame.dependencyEnvironment] using
      And.intro entry.frame.valid (And.intro entry.frame_environment_le ih)

noncomputable def OriginalRichFrame.group
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (capturedOrdered : sourceEnv.Ordered) (ownerInitial : List Closure)
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)) :
    OriginalRichFrame headerEnv env U registry target (.cons context domain) (Locals.push headerLocals)
      (declaredLeft.cons leftValue) (declaredRight.cons rightValue)
      (headerAvailable.push (entries.flatMap (fun entry => captureNeeds entry.input))) :=
  ⟨.group tail.raw domain capturedOrdered ownerInitial (richGroupedEntriesRaw entries),
    by simpa only [RawOriginalRichFrame.Valid] using And.intro tail.valid (richGroupedEntriesRaw_valid entries)⟩

/-- A whole source cut carries this actual frame, not only a raw substitution
and a valuation. Its budget is tied to the retained ORIGINAL location. -/
structure OriginalRichOccurrenceFrame
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    (location : Located root node) (initialContext : ContextDerivation sourceEnv U source)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (ordered : sourceEnv.Ordered) (initialEnvironment : List Closure) where
  frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initialContext) locals σ τ available
  substitutions : Ctx.SubstEq env U target σ τ occurrenceSource
  environment_le : environmentCost (frame.dependencyEnvironment ordered) ≤
    environmentCost (location.dependencyEnvironment ordered initialEnvironment)

/-- No arbitrary scalar budget is supplied: the comparison is between the
actual semantic frame and the actual original path environment. -/
theorem OriginalRichOccurrenceFrame.cost_le
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    (Closure.close (node.dependencyOrigin ordered) (occurrence.frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (root.dependencyOrigin ordered) initialEnvironment).cost := by
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left occurrence.environment_le _))
    (location.dependency_cost_le ordered initialEnvironment)

/-- Actual lookup at an arbitrary freshly bound ORIGINAL domain. It works
for open source contexts and rich domain certificates containing projections. -/
theorem OriginalRichFrame.lookupHead
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (member : need ∈ needs) :
    ∃ resultSupport, Nonempty (RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (resultSupport : Profile need.rank) footprint) ∧ footprint.Available available ∧
      need.profile.HasType resultSupport ∧
      Related env U registry target x y (A.subst σ) need.profile resultSupport := by
  have bound := bounded need member
  have included := covered need member
  simp only [Need.atGrade, dif_pos bound] at included
  have selected : Related env U registry target x y (A.subst σ) (raiseProfile n bound need.profile) support :=
    Related.of_singletons (fun atom hm => arguments.singleton_of_mem (included atom hm))
  exact ⟨_, ⟨certificate.lower need.rank bound⟩, resources,
    lowerProfile.hasType bound (typed_subset included typed), lowerProfile.related bound henv formed selected⟩

/-- Enter a real original Pi binder. The body frame retains the fresh
semantic binder and the complete rich domain query. Its environment bound
is derived from the parent occurrence, not supplied by a cut callback. -/
noncomputable def OriginalRichOccurrenceFrame.piBody
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.pi hu hv domain body)}
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
    OriginalRichOccurrenceFrame (.piBody location) initialContext env registry target (Locals.push locals)
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

/-- Start at an arbitrary original source context. The base closure is the
actual semantic frame environment, so no closed declaration root is needed. -/
noncomputable def OriginalRichOccurrenceFrame.here
    (root : EndpointRef sourceEnv U source expression assigned)
    (context : ContextDerivation sourceEnv U source)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    OriginalRichOccurrenceFrame (.here (root := root)) context env registry target locals σ τ available
      ordered (frame.dependencyEnvironment ordered) :=
  ⟨frame, substitutions, Nat.le_refl _⟩

noncomputable def OriginalRichOccurrenceFrame.appFunction
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {function : EndpointState sourceEnv U occurrenceSource f (.forallE A B)}
    {argument : EndpointState sourceEnv U occurrenceSource a A}
    {result : EndpointState sourceEnv U occurrenceSource (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.app hu hv domain body function argument result)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame (.appFunction location) initialContext env registry target locals σ τ available
      ordered initialEnvironment :=
  ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.appArgument
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U occurrenceSource A (.sort u)}
    {body : EndpointState sourceEnv U (A :: occurrenceSource) B (.sort v)}
    {function : EndpointState sourceEnv U occurrenceSource f (.forallE A B)}
    {argument : EndpointState sourceEnv U occurrenceSource a A}
    {result : EndpointState sourceEnv U occurrenceSource (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.app hu hv domain body function argument result)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame (.appArgument location) initialContext env registry target locals σ τ available
      ordered initialEnvironment :=
  ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
