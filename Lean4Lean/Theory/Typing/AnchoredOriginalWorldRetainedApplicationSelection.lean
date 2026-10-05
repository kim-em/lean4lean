import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding

/-! Select the same annotated operands and their original prefix route jointly.
Universe/profile operations remain in the finite output path. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private GeneralOutputPath.lowerRaised from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- A charged leaf retains the literal recipe, rather than a newly allocated
`.action (.select ...)` wrapper. Selection is a separate finite cursor. -/
structure RetainedChargedAppOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.app f a) assigned
  location : Located root node
  relevant : Bool
  rank : Nat
  profile : Profile rank
  output : Atom rank
  selected : output ∈ profile.atoms
  footprint : Footprint
  recipe : RichCodeRecipe env U registry target source locals σ (.app f a)
    relevant profile footprint

inductive RetainedApplicationOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  | original (origin : RichAppOrigin root env registry target source locals σ f a)
  | charged (origin : RetainedChargedAppOrigin root env registry target source locals σ f a)

def RetainedApplicationOrigin.rank
    (origin : RetainedApplicationOrigin root env registry target source locals σ f a) : Nat :=
  match origin with | .original origin => origin.rank | .charged origin => origin.rank

def RetainedApplicationOrigin.output
    (origin : RetainedApplicationOrigin root env registry target source locals σ f a) : Atom origin.rank :=
  match origin with | .original origin => origin.output | .charged origin => origin.output

def RetainedApplicationOrigin.footprint
    (origin : RetainedApplicationOrigin root env registry target source locals σ f a) : Footprint :=
  match origin with
  | .original origin => origin.functionFootprint ++ origin.argumentFootprint
  | .charged origin => origin.footprint

def RetainedApplicationOrigin.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedApplicationOrigin root env registry target source locals σ f a)
    (start : EndpointState sourceEnv U source (.app f a) assigned) : Prop :=
  match origin with
  | .original origin => origin.RootedAt start
  | .charged origin => Nonempty (PrefixRoute sourceEnv U source (.app f a) start origin.node)

theorem RetainedApplicationOrigin.RootedAt.prepend
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RetainedApplicationOrigin root env registry target source locals σ f a}
    (rooted : origin.RootedAt middle)
    (path : PrefixRoute sourceEnv U source (.app f a) start middle) : origin.RootedAt start := by
  cases origin with
  | original origin => obtain ⟨route⟩ := rooted; exact ⟨path.append route⟩
  | charged origin => obtain ⟨route⟩ := rooted; exact ⟨path.append route⟩

inductive RetainedApplicationWorlds (strata : EquationStratification env) :
    RetainedApplicationOrigin root env registry target source locals σ f a → Type where
  | original {origin : RichAppOrigin root env registry target source locals σ f a}
      (annotation : RichAppWorlds strata origin) : RetainedApplicationWorlds strata (.original origin)
  | charged {origin : RetainedChargedAppOrigin root env registry target source locals σ f a}
      (annotation : WorldCodeRecipeProvenance strata origin.recipe) :
      RetainedApplicationWorlds strata (.charged origin)

noncomputable def RetainedApplicationWorlds.worlds
    (annotation : RetainedApplicationWorlds strata origin) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with | .original children => children.worlds | .charged child => child.worlds

noncomputable def RetainedApplicationOrigin.headDepth
    (origin : RetainedApplicationOrigin root env registry target source locals σ f a)
    (policy : Name → Nat → Nat) : Nat :=
  match origin with
  | .original origin => max (origin.function.headDepth policy) (origin.argument.headDepth policy)
  | .charged origin => origin.recipe.headDepth policy

private theorem retainedCodeOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, annotation, ⟨path⟩, included, sponsored, rooted, depth⟩ := origins a ha
  exact ⟨origin, annotation, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, sponsored, rooted, depth⟩

mutual
theorem WorldObsProvenance.retainedApplicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortablePrefix (applicationPrefix location) origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored, ⟨(applicationPrefix location).route⟩,
      fun policy => by simpa only [RetainedApplicationOrigin.headDepth, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, _, _, .code source, location =>
    try simp only [RichObs.headDepth]
    exact source.retainedApplicationOrigin location member
  | _, _, _, _, .app hu hv domain codomain function argumentNode result,
      .app _ _ fn argument arguments admitted, .app _ _ fnProvenance argProvenance _ _, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    let origin : RichAppOrigin root env registry target source locals σ f arg :=
      ⟨_, _, _, _, hu, hv, _, _, _, _, _, location, _, _, _, _, _, fn, _, argument, arguments, admitted⟩
    exact ⟨.original origin, .original ⟨fnProvenance, argProvenance⟩, ⟨.refl⟩, fun _ h => h, fun _ h => h, ⟨.done _⟩, fun policy => by simp only [origin]; exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, depth⟩ :=
      source.retainedApplicationOrigin (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichObs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, depth⟩ := left.retainedApplicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, depth⟩ := right.retainedApplicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := source.retainedApplicationOrigin location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, depth⟩
  | _, _, _, _, _, _, .unpad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := source.retainedApplicationOrigin location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, rooted, depth⟩
  | _, _, _, _, _, _, .view source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := source.retainedApplicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, rooted, depth⟩
  | _, _, _, _, _, _, .select source selected, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    exact source.retainedApplicationOrigin location selected
  | _, _, _, _, _, _, .action source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := source.retainedApplicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path change⟩, included, sponsored, rooted, depth⟩
  | _, _, _, _, _, _, .castProfile equal child, location =>
    try simp only [RichObs.headDepth]
    have selected := member
    rw [← equal] at selected
    obtain ⟨origin, children, path, included, sponsored, rooted, depth⟩ :=
      child.retainedApplicationOrigin location selected
    refine ⟨origin, children, path, included, sponsored, rooted, ?_⟩
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
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := child.retainedApplicationOrigin location high
    exact ⟨origin, children, ⟨GeneralOutputPath.lowerRaised bound path⟩, included, sponsored, rooted,
      fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩

termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldCertProvenance.retainedApplicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint}
    (annotation : WorldCertProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortablePrefix (applicationPrefix location) origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored, ⟨(applicationPrefix location).route⟩,
      fun policy => by simpa only [RetainedApplicationOrigin.headDepth, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, node, .recipe code, .recipe child, location =>
    let origin : RetainedChargedAppOrigin root env registry target source locals σ f arg :=
      { assigned := _, node := node, location := location, relevant := _, rank := _,
        profile := _, output := atom, selected := member, footprint := _, recipe := code }
    exact ⟨.charged origin, .charged child,
      ⟨.refl⟩, (fun _ h => h), (fun _ h => h), ⟨.done _⟩, fun policy => by
        simp only [RetainedApplicationOrigin.headDepth, RichCert.headDepth, origin, RichCodeRecipe.headDepth]
        exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .observe source _, location =>
    try simp only [RichCert.headDepth]
    exact source.retainedApplicationOrigin location member
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, depth⟩ :=
      source.retainedApplicationOrigin (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, depth⟩ := left.retainedApplicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, depth⟩ := right.retainedApplicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, depth⟩ := source.retainedApplicationOrigin location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, depth⟩
  | _, _, _, _, _, _, .down (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedCodeOrigin .down value.formed (fun _ h => source.retainedApplicationOrigin location h) member
  | _, _, _, _, _, _, .map view (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedCodeOrigin (.map view) value.formed (fun _ h => source.retainedApplicationOrigin location h) member
  | _, _, _, _, _, _, .support action (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedCodeOrigin (.support action) value.formed (fun _ h => source.retainedApplicationOrigin location h) member
  | _, _, _, _, _, _, .select (certificate := value) source selected, location =>
    try simp only [RichCert.headDepth]
    exact retainedCodeOrigin (.select selected) value.formed (fun _ h => source.retainedApplicationOrigin location h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
