import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

/-! Joint literal selection for a projection observer. A selected result is
an actual native projection with its original children, or the exact retained
charged recipe. No physical projection is inferred from a recipe certificate.
All finite output operations and world annotations remain attached. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

private theorem retainedLegacyProjectionEmpty
    (observation : Obs env U registry target locals σ (.proj name index major) demand footprint) :
    demand = .empty := by
  match observation with
  | .empty => rfl
  | .union left right => rw [retainedLegacyProjectionEmpty left, retainedLegacyProjectionEmpty right]; rfl
  | .view child change => have impossible := retainedLegacyProjectionEmpty child; cases impossible
  | .pad child => rw [retainedLegacyProjectionEmpty child]; rfl
  | .unpad child =>
    have equal := congrArg Profile.down (retainedLegacyProjectionEmpty child)
    simpa only [Profile.down_pad, Profile.down_empty] using equal
  | .rowShift child => have impossible := retainedLegacyProjectionEmpty child; cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

private theorem codeNoAtom
    (action : SortableCodeAction env U registry target relevant p next q)
    (none : ∀ a ∈ p.atoms, False) (member : b ∈ q.atoms) : False := by
  obtain ⟨a, ha, _⟩ := action.atom member
  exact none a ha

mutual
private theorem CodeCert.retainedProjectionNoAtom
    {demand : Profile n}
    (query : CodeCert env U registry target locals σ (.proj name index value) demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .seed source _ => rw [retainedLegacyProjectionEmpty source] at member; cases member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.retainedProjectionNoAtom) (right.retainedProjectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.retainedProjectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.retainedProjectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .familyPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) .familyPad (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .down source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) .down (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .map view source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.map view) (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .select source selected => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.select selected) (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.focusMinimal minimal bound) (fun _ h => source.retainedProjectionNoAtom h) member
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

private theorem SortableObs.retainedProjectionNoAtom
    {demand : Profile n}
    (query : SortableObs env U registry target locals σ (.proj name index value) demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .legacy source => rw [retainedLegacyProjectionEmpty source] at member; cases member
  | _, _, _, .code _ source => exact source.retainedProjectionNoAtom member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.retainedProjectionNoAtom) (right.retainedProjectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.retainedProjectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.retainedProjectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .view source _ | _, _, _, .action source _ | _, _, _, .rowShift source =>
    exact source.retainedProjectionNoAtom (List.mem_singleton_self _)
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

private theorem SortableCert.retainedProjectionNoAtom
    {demand : Profile n}
    (query : SortableCert env U registry target locals σ (.proj name index value) relevant demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .ofCode source _ => exact source.retainedProjectionNoAtom member
  | _, _, _, .observe source _ => exact source.retainedProjectionNoAtom member
  | _, _, _, .seed source _ => rw [retainedLegacyProjectionEmpty source] at member; cases member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.retainedProjectionNoAtom) (right.retainedProjectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.retainedProjectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.retainedProjectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .familyPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .familyPad (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .down source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .down (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .map view source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.map view) (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .select source selected => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.select selected) (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.focusMinimal minimal bound) (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .sortPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .sortPad (fun _ h => source.retainedProjectionNoAtom h) member
  | _, _, _, .support action source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.support action) (fun _ h => source.retainedProjectionNoAtom h) member
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
open private GeneralOutputPath.lowerRaised from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

/-- The actual field certificate either supports the whole original request,
with its original domain chain, or the selected sortable output. In the latter
case the request itself is unchanged; the selector retains the finite output
path separately. -/
inductive RetainedProjectionFieldUse
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (request : DataRequest (Profile n)) (fieldType : VExpr) :
    {m : Nat} → Profile m → Type where
  | direct (alignment : DomainChain env U registry target request.input request.domain fieldType) :
      RetainedProjectionFieldUse env U registry target request fieldType request.input
  | sortable {output : Atom m} {relevant : Bool}
      (formed : (Profile.singleton output).HasType (.sort relevant)) :
      RetainedProjectionFieldUse env U registry target request fieldType (.singleton output)

structure RetainedNativeProjectionOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (name : Name) (index : Nat) (value : VExpr) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.proj name index value) assigned
  location : Located root node
  head : ProjectionHead node
  rank : Nat
  record : RecordData (Profile rank)
  request : DataRequest (Profile rank)
  nameEq : record.family.name = name
  member : (index, request) ∈ record.fields
  fieldRank : Nat
  fieldInput : Profile fieldRank
  support : Profile fieldRank
  majorFootprint : Footprint
  fieldFootprint : Footprint
  majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
    (Profile.singleton (n := rank + 1) (.record record)) majorFootprint
  fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint
  typed : fieldInput.HasType support
  fieldUse : RetainedProjectionFieldUse env U registry target request (head.fieldType.subst σ) fieldInput
  output : Atom rank
  selected : output ∈ request.input.atoms

structure RetainedChargedProjectionOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (name : Name) (index : Nat) (value : VExpr) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.proj name index value) assigned
  location : Located root node
  relevant : Bool
  rank : Nat
  profile : Profile rank
  output : Atom rank
  selected : output ∈ profile.atoms
  footprint : Footprint
  recipe : RichCodeRecipe env U registry target source locals σ (.proj name index value)
    relevant profile footprint

inductive RetainedProjectionOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (name : Name) (index : Nat) (value : VExpr) where
  | original (origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value)
  | charged (origin : RetainedChargedProjectionOrigin root env registry target source locals σ name index value)

def RetainedProjectionOrigin.rank
    (origin : RetainedProjectionOrigin root env registry target source locals σ name index value) : Nat :=
  match origin with | .original origin => origin.rank | .charged origin => origin.rank

def RetainedProjectionOrigin.output
    (origin : RetainedProjectionOrigin root env registry target source locals σ name index value) : Atom origin.rank :=
  match origin with | .original origin => origin.output | .charged origin => origin.output

def RetainedProjectionOrigin.footprint
    (origin : RetainedProjectionOrigin root env registry target source locals σ name index value) : Footprint :=
  match origin with
  | .original origin => origin.majorFootprint ++ origin.fieldFootprint
  | .charged origin => origin.footprint

def RetainedProjectionOrigin.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedProjectionOrigin root env registry target source locals σ name index value)
    (start : EndpointState sourceEnv U source (.proj name index value) assigned) : Prop :=
  match origin with
  | .original origin => Nonempty (PrefixRoute sourceEnv U source (.proj name index value) start
      (projectionNatural origin.head))
  | .charged origin => Nonempty (PrefixRoute sourceEnv U source (.proj name index value) start origin.node)

theorem RetainedProjectionOrigin.RootedAt.prepend
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RetainedProjectionOrigin root env registry target source locals σ name index value}
    (rooted : origin.RootedAt middle)
    (path : PrefixRoute sourceEnv U source (.proj name index value) start middle) : origin.RootedAt start := by
  cases origin with
  | original origin => obtain ⟨route⟩ := rooted; exact ⟨path.append route⟩
  | charged origin => obtain ⟨route⟩ := rooted; exact ⟨path.append route⟩

structure RetainedProjectionChildren (strata : EquationStratification env)
    (origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value) where
  major : WorldObsProvenance strata origin.majorQuery
  field : WorldCertProvenance strata origin.fieldCode
  majorSite : WorldQuerySite (registry := registry) (target := target) strata
    (.ref (.right origin.head.major)) locals σ
  fieldSite : WorldQuerySite (registry := registry) (target := target) strata origin.head.field locals σ

noncomputable def RetainedProjectionChildren.worlds (children : RetainedProjectionChildren strata origin) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  children.majorSite.worlds ++ children.fieldSite.worlds ++ children.major.worlds ++ children.field.worlds

inductive RetainedProjectionWorlds (strata : EquationStratification env) :
    RetainedProjectionOrigin root env registry target source locals σ name index value → Type where
  | original {origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value}
      (annotation : RetainedProjectionChildren strata origin) : RetainedProjectionWorlds strata (.original origin)
  | charged {origin : RetainedChargedProjectionOrigin root env registry target source locals σ name index value}
      (annotation : WorldCodeRecipeProvenance strata origin.recipe) :
      RetainedProjectionWorlds strata (.charged origin)

noncomputable def RetainedProjectionWorlds.worlds
    (annotation : RetainedProjectionWorlds strata origin) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with | .original children => children.worlds | .charged child => child.worlds

noncomputable def RetainedProjectionOrigin.headDepth
    (origin : RetainedProjectionOrigin root env registry target source locals σ name index value)
    (policy : Name → Nat → Nat) : Nat :=
  match origin with
  | .original origin => max (origin.majorQuery.headDepth policy) (origin.fieldCode.headDepth policy)
  | .charged origin => origin.recipe.headDepth policy

/-- Only charged leaves recurse into another recipe. This is the size of
that exact retained annotation, not a size assigned to an F result. -/
noncomputable def RetainedProjectionWorlds.retainedSize
    (annotation : RetainedProjectionWorlds strata origin) : Nat :=
  match annotation with
  | .original _ => 0
  | .charged child => sizeOf child

private theorem retainedSizedCodeOrigin
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    {budget : Nat}
    (origins : ∀ a ∈ p.atoms, ∃ origin : RetainedProjectionOrigin root env registry target source locals σ name index value,
      ∃ annotation : RetainedProjectionWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧ annotation.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ origin : RetainedProjectionOrigin root env registry target source locals σ name index value,
      ∃ annotation : RetainedProjectionWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧ annotation.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, annotation, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := origins a ha
  exact ⟨origin, annotation, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, sponsored, rooted, smaller, depth⟩

mutual
theorem WorldObsProvenance.retainedProjectionOriginSized
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {demand : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms)
    {budget : Nat} (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ origin : RetainedProjectionOrigin root env registry target source locals σ name index value,
      ∃ children : RetainedProjectionWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy legacy child, location =>
    exact False.elim (legacy.retainedProjectionNoAtom member)
  | _, _, _, _, _, _, .code source, location =>
    try simp only [RichObs.headDepth]
    exact source.retainedProjectionOriginSized (budget := budget) location member
  | _, _, _, _, _, _,
      @WorldObsProvenance.projection _ _ _ _ _ _ _ _ _ rank _ _ _ _ _ support _ _ record request
        head nameEq fieldMember majorQuery fieldCode
        majorAnnotation fieldAnnotation majorSite fieldSite typed alignment, location =>
    try simp only [RichObs.headDepth]
    let origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value :=
      { assigned := _, node := _, location := location, head := head
        rank := rank, record := record, request := request, nameEq := nameEq, member := fieldMember
        fieldRank := rank, fieldInput := request.input, support := support
        majorFootprint := _, fieldFootprint := _, majorQuery := majorQuery, fieldCode := fieldCode
        typed := typed, fieldUse := .direct alignment, output := atom, selected := member }
    exact ⟨.original origin, .original ⟨majorAnnotation, fieldAnnotation, majorSite, fieldSite⟩,
      ⟨.refl⟩, (fun _ h => h), (fun _ h => h), ⟨head.route⟩,
      (by simp only [RetainedProjectionWorlds.retainedSize]; simp only [WorldObsProvenance.projection.sizeOf_spec] at sizeBound; omega),
      fun policy => Nat.le_refl _⟩
  | _, _, _, _, _, _,
      @WorldObsProvenance.projectionSortable _ _ _ _ _ _ _ _ _ rank _ _ _ _ _ fieldRank _ support _ _ record request
        head nameEq fieldMember majorQuery requestAtom resultAtom selected path sortable fieldCode
        majorAnnotation fieldAnnotation majorSite fieldSite typed, location =>
    cases List.mem_singleton.mp member
    try simp only [RichObs.headDepth]
    let origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value :=
      { assigned := _, node := _, location := location, head := head
        rank := rank, record := record, request := request, nameEq := nameEq, member := fieldMember
        fieldRank := fieldRank, fieldInput := .singleton resultAtom, support := support
        majorFootprint := _, fieldFootprint := _, majorQuery := majorQuery, fieldCode := fieldCode
        typed := typed, fieldUse := .sortable sortable, output := requestAtom, selected := selected }
    exact ⟨.original origin, .original ⟨majorAnnotation, fieldAnnotation, majorSite, fieldSite⟩,
      ⟨path⟩, (fun _ h => h), (fun _ h => h), ⟨head.route⟩,
      (by simp only [RetainedProjectionWorlds.retainedSize]; simp only [WorldObsProvenance.projectionSortable.sizeOf_spec] at sizeBound; omega),
      fun policy => Nat.le_refl _⟩
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, smaller, depth⟩ :=
      source.retainedProjectionOriginSized (budget := budget) (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichObs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := left.retainedProjectionOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := right.retainedProjectionOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedProjectionOriginSized (budget := budget) location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .unpad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedProjectionOriginSized (budget := budget) location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .view source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedProjectionOriginSized (budget := budget) location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .select source selected, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    exact source.retainedProjectionOriginSized (budget := budget) location selected
  | _, _, _, _, _, _, .action source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedProjectionOriginSized (budget := budget) location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path change⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .castProfile equal child, location =>
    try simp only [RichObs.headDepth]
    have selected := member
    rw [← equal] at selected
    obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ :=
      child.retainedProjectionOriginSized (budget := budget) location selected
    refine ⟨origin, children, path, included, sponsored, rooted, smaller, ?_⟩
    cases equal
    exact depth
  | _, _, _, _, _, _, .lowerRaised (profile := profile) (N := N) (bound := bound) child, location =>
    try simp only [RichObs.headDepth]
    have high : raiseAtom N bound atom ∈ (raiseProfile N bound profile).atoms := by
      have selected : List.Subset (Profile.singleton atom).atoms profile.atoms := by
        intro a present; cases List.mem_singleton.mp present; exact member
      apply raiseProfile_subset bound selected
      simp only [raiseProfile_singleton]
      exact List.mem_singleton_self _
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := child.retainedProjectionOriginSized (budget := budget) location high
    exact ⟨origin, children, ⟨GeneralOutputPath.lowerRaised bound path⟩, included, sponsored, rooted, smaller,
      fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩

termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldCertProvenance.retainedProjectionOriginSized
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {demand : Profile n}
    {query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint}
    (annotation : WorldCertProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms)
    {budget : Nat} (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ origin : RetainedProjectionOrigin root env registry target source locals σ name index value,
      ∃ children : RetainedProjectionWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy legacy child, location =>
    exact False.elim (legacy.retainedProjectionNoAtom member)
  | _, _, _, _, node, .recipe code, .recipe child, location =>
    let origin : RetainedChargedProjectionOrigin root env registry target source locals σ name index value :=
      { assigned := _, node := node, location := location, relevant := _, rank := _,
        profile := _, output := atom, selected := member, footprint := _, recipe := code }
    exact ⟨.charged origin, .charged child,
      ⟨.refl⟩, (fun _ h => h), (fun _ h => h), ⟨.done _⟩, (by simp only [RetainedProjectionWorlds.retainedSize]; try simp only [WorldCertProvenance.recipe.sizeOf_spec] at sizeBound; omega), fun policy => by
        simp only [RetainedProjectionOrigin.headDepth, RichCert.headDepth, origin]
        exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .observe source _, location =>
    try simp only [RichCert.headDepth]
    exact source.retainedProjectionOriginSized (budget := budget) location member
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, smaller, depth⟩ :=
      source.retainedProjectionOriginSized (budget := budget) (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := left.retainedProjectionOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := right.retainedProjectionOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedProjectionOriginSized (budget := budget) location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .down (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin .down value.formed (fun _ h => source.retainedProjectionOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .map view (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.map view) value.formed (fun _ h => source.retainedProjectionOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .support action (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.support action) value.formed (fun _ h => source.retainedProjectionOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .select (certificate := value) source selected, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.select selected) value.formed (fun _ h => source.retainedProjectionOriginSized (budget := budget) location h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
