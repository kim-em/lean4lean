import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationSelection

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

/-- Only charged leaves recurse into another recipe. This is the size of
that exact retained annotation, not a size assigned to an F result. -/
noncomputable def RetainedApplicationWorlds.retainedSize
    (annotation : RetainedApplicationWorlds strata origin) : Nat :=
  match annotation with
  | .original _ => 0
  | .charged child => sizeOf child

private theorem retainedSizedCodeOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    {budget : Nat}
    (origins : ∀ a ∈ p.atoms, ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧ annotation.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      origin.RootedAt node ∧ annotation.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, annotation, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := origins a ha
  exact ⟨origin, annotation, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, sponsored, rooted, smaller, depth⟩

mutual
theorem WorldObsProvenance.retainedApplicationOriginSized
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms)
    {budget : Nat} (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortablePrefix (applicationPrefix location) origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored, ⟨(applicationPrefix location).route⟩, (by simp only [RetainedApplicationWorlds.retainedSize]; simp +zetaDelta at sizeBound; omega),
      fun policy => by simpa only [RetainedApplicationOrigin.headDepth, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, _, _, .code source, location =>
    try simp only [RichObs.headDepth]
    exact source.retainedApplicationOriginSized (budget := budget) location member
  | _, _, _, _, .app hu hv domain codomain function argumentNode result,
      .app _ _ fn argument arguments admitted, .app _ _ fnProvenance argProvenance _ _, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    let origin : RichAppOrigin root env registry target source locals σ f arg :=
      ⟨_, _, _, _, hu, hv, _, _, _, _, _, location, _, _, _, _, _, fn, _, argument, arguments, admitted⟩
    exact ⟨.original origin, .original ⟨fnProvenance, argProvenance⟩, ⟨.refl⟩, fun _ h => h, fun _ h => h, ⟨.done _⟩, (by simp only [RetainedApplicationWorlds.retainedSize]; simp +zetaDelta at sizeBound; omega), fun policy => by simp only [origin]; exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, smaller, depth⟩ :=
      source.retainedApplicationOriginSized (budget := budget) (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichObs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := left.retainedApplicationOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := right.retainedApplicationOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedApplicationOriginSized (budget := budget) location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .unpad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedApplicationOriginSized (budget := budget) location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .view source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedApplicationOriginSized (budget := budget) location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .select source selected, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    exact source.retainedApplicationOriginSized (budget := budget) location selected
  | _, _, _, _, _, _, .action source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedApplicationOriginSized (budget := budget) location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path change⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .castProfile equal child, location =>
    try simp only [RichObs.headDepth]
    have selected := member
    rw [← equal] at selected
    obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ :=
      child.retainedApplicationOriginSized (budget := budget) location selected
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
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := child.retainedApplicationOriginSized (budget := budget) location high
    exact ⟨origin, children, ⟨GeneralOutputPath.lowerRaised bound path⟩, included, sponsored, rooted, smaller,
      fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩

termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldCertProvenance.retainedApplicationOriginSized
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint}
    (annotation : WorldCertProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms)
    {budget : Nat} (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ origin : RetainedApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < budget ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortablePrefix (applicationPrefix location) origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored, ⟨(applicationPrefix location).route⟩, (by simp only [RetainedApplicationWorlds.retainedSize]; simp +zetaDelta at sizeBound; omega),
      fun policy => by simpa only [RetainedApplicationOrigin.headDepth, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, node, .recipe code, .recipe child, location =>
    let origin : RetainedChargedAppOrigin root env registry target source locals σ f arg :=
      { assigned := _, node := node, location := location, relevant := _, rank := _,
        profile := _, output := atom, selected := member, footprint := _, recipe := code }
    exact ⟨.charged origin, .charged child,
      ⟨.refl⟩, (fun _ h => h), (fun _ h => h), ⟨.done _⟩, (by simp only [RetainedApplicationWorlds.retainedSize]; try simp only [WorldCertProvenance.recipe.sizeOf_spec] at sizeBound; omega), fun policy => by
        simp only [RetainedApplicationOrigin.headDepth, RichCert.headDepth, origin, RichCodeRecipe.headDepth]
        exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .observe source _, location =>
    try simp only [RichCert.headDepth]
    exact source.retainedApplicationOriginSized (budget := budget) location member
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, output, included, sponsored, rooted, smaller, depth⟩ :=
      source.retainedApplicationOriginSized (budget := budget) (path.locate location) member
    exact ⟨origin, children, output, included, sponsored, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := left.retainedApplicationOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, rooted, smaller, depth⟩ := right.retainedApplicationOriginSized (budget := budget) location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, rooted, smaller, depth⟩ := source.retainedApplicationOriginSized (budget := budget) location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .down (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin .down value.formed (fun _ h => source.retainedApplicationOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .map view (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.map view) value.formed (fun _ h => source.retainedApplicationOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .support action (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.support action) value.formed (fun _ h => source.retainedApplicationOriginSized (budget := budget) location h) member
  | _, _, _, _, _, _, .select (certificate := value) source selected, location =>
    try simp only [RichCert.headDepth]
    exact retainedSizedCodeOrigin (.select selected) value.formed (fun _ h => source.retainedApplicationOriginSized (budget := budget) location h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
