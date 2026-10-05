import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationOrigins

/-! Application extraction keeps provenance for the SAME actual child
queries. Their retained foreign worlds are subsets of the incoming query's
worlds; endpoint cost descent alone is not used to discard those sponsors. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure SortableAppWorlds (strata : EquationStratification env)
    (origin : SortableAppOrigin env U registry target locals σ f a) where
  function : WorldSortableObsProvenance strata origin.function
  argument : WorldSortableObsProvenance strata origin.argument

noncomputable def SortableAppWorlds.worlds
    (annotation : SortableAppWorlds strata origin) : List (EquationWorldClosureOrder.World strata.rules.length) := annotation.function.worlds ++ annotation.argument.worlds

structure RichAppWorlds (strata : EquationStratification env)
    (origin : RichAppOrigin root env registry target source locals σ f a) where
  function : WorldObsProvenance strata origin.function
  argument : WorldObsProvenance strata origin.argument

noncomputable def RichAppWorlds.worlds
    (annotation : RichAppWorlds strata origin) : List (EquationWorldClosureOrder.World strata.rules.length) := annotation.function.worlds ++ annotation.argument.worlds

inductive RichApplicationWorlds (strata : EquationStratification env) :
    RichApplicationOrigin root env registry target source locals σ f a → Type where
  | original {origin : RichAppOrigin root env registry target source locals σ f a}
      (annotation : RichAppWorlds strata origin) : RichApplicationWorlds strata (.original origin)
  | charged {origin : RichChargedAppOrigin root env registry target source locals σ f a}
      (annotation : WorldCodeRecipeProvenance strata origin.recipe) :
      RichApplicationWorlds strata (.charged origin)

noncomputable def RichApplicationWorlds.worlds
    (annotation : RichApplicationWorlds strata origin) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .original children => children.worlds
  | .charged recipe => recipe.worlds

noncomputable def RichApplicationOrigin.headDepth
    (origin : RichApplicationOrigin root env registry target source locals σ f a)
    (policy : Name → Nat → Nat) : Nat :=
  match origin with
  | .original physical => max (physical.function.headDepth policy) (physical.argument.headDepth policy)
  | .charged packet => packet.recipe.headDepth policy

private theorem sortableCodeOrigin
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ annotation : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset annotation.worlds worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ annotation : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset annotation.worlds worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ incomingDepth policy := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, annotation, ⟨path⟩, included, sponsored, depth⟩ := origins a ha
  exact ⟨origin, annotation, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, sponsored, depth⟩

mutual
theorem WorldLegacyObsProvenance.applicationOrigin
    {demand : Profile n}
    {query : Obs env U registry target locals σ (.app f arg) demand footprint}
    (annotation : WorldLegacyObsProvenance strata query) (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ children : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .empty =>
    try simp only [Obs.headDepth]
    cases member
  | _, _, _, _, .app fn argument arguments admitted fnProvenance argProvenance =>
    try simp only [Obs.headDepth]
    cases List.mem_singleton.mp member
    let origin : SortableAppOrigin env U registry target locals σ f arg :=
      ⟨_, _, _, _, _, (.legacy fn), _, (.legacy argument), arguments.toGeneral, admitted⟩
    exact ⟨origin, ⟨(.legacy fn fnProvenance), (.legacy argument argProvenance)⟩, ⟨.refl⟩, fun _ h => h, fun _ h => h, fun policy => by simp only [origin, SortableObs.headDepth]; exact Nat.le_refl _⟩
  | _, _, _, _, .union _ _ left right =>
    try simp only [Obs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, .pad _ source =>
    try simp only [Obs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .unpad _ source =>
    try simp only [Obs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .view _ change source =>
    try simp only [Obs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, depth⟩
  | _, _, _, _, .rowShift _ source =>
    try simp only [Obs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included, sponsored, depth⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldLegacyCertProvenance.applicationOrigin
    {demand : Profile n}
    {query : CodeCert env U registry target locals σ (.app f arg) demand footprint}
    (annotation : WorldLegacyCertProvenance strata query) (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ children : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .seed _ _ source =>
    try simp only [CodeCert.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .union _ _ left right =>
    try simp only [CodeCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, .pad _ source =>
    try simp only [CodeCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .unpad _ source =>
    try simp only [CodeCert.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .familyPad value source =>
    try simp only [CodeCert.headDepth]
    exact sortableCodeOrigin .familyPad value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .down value source =>
    try simp only [CodeCert.headDepth]
    exact sortableCodeOrigin .down value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .map v value source =>
    try simp only [CodeCert.headDepth]
    exact sortableCodeOrigin (.map v) value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .select value selected source =>
    try simp only [CodeCert.headDepth]
    exact sortableCodeOrigin (.select selected) value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .focusMinimal value minimal bound source =>
    try simp only [CodeCert.headDepth]
    exact sortableCodeOrigin (.focusMinimal minimal bound) value.formed (fun _ h => source.applicationOrigin h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldSortableObsProvenance.applicationOrigin
    {demand : Profile n}
    {query : SortableObs env U registry target locals σ (.app f arg) demand footprint}
    (annotation : WorldSortableObsProvenance strata query) (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ children : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .legacy _ source =>
    try simp only [SortableObs.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .code _ _ source =>
    try simp only [SortableObs.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .app fn argument arguments admitted fnProvenance argProvenance =>
    try simp only [SortableObs.headDepth]
    cases List.mem_singleton.mp member
    let origin : SortableAppOrigin env U registry target locals σ f arg :=
      ⟨_, _, _, _, _, fn, _, argument, arguments, admitted⟩
    exact ⟨origin, ⟨fnProvenance, argProvenance⟩, ⟨.refl⟩, fun _ h => h, fun _ h => h, fun policy => by simp only [origin]; exact Nat.le_refl _⟩
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableObs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, .pad _ source =>
    try simp only [SortableObs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .unpad _ source =>
    try simp only [SortableObs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .view _ change source =>
    try simp only [SortableObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, depth⟩
  | _, _, _, _, .action _ change source =>
    try simp only [SortableObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path change⟩, included, sponsored, depth⟩
  | _, _, _, _, .rowShift _ source =>
    try simp only [SortableObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included, sponsored, depth⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldSortableCertProvenance.applicationOrigin
    {demand : Profile n}
    {query : SortableCert env U registry target locals σ (.app f arg) relevant demand footprint}
    (annotation : WorldSortableCertProvenance strata query) (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry target locals σ f arg,
      ∃ children : SortableAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .ofCode _ _ source =>
    try simp only [SortableCert.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .observe _ _ source =>
    try simp only [SortableCert.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .seed _ _ source =>
    try simp only [SortableCert.headDepth]
    exact source.applicationOrigin member
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, .pad _ source =>
    try simp only [SortableCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .unpad _ source =>
    try simp only [SortableCert.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, depth⟩
  | _, _, _, _, .familyPad value source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin .familyPad value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .down value source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin .down value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .map v value source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin (.map v) value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .select value selected source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin (.select selected) value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .focusMinimal value minimal bound source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin (.focusMinimal minimal bound) value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .sortPad value source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin .sortPad value.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, _, .support action value source =>
    try simp only [SortableCert.headDepth]
    exact sortableCodeOrigin (.support action) value.formed (fun _ h => source.applicationOrigin h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega
end

private noncomputable def GeneralOutputPath.lowerRaised
    {a : Atom n} (bound : n ≤ N)
    (path : GeneralOutputPath env U registry target source (raiseAtom N bound a)) :
    GeneralOutputPath env U registry target source a := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact path
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n; simpa only [raiseAtom_self] using path
    · have previous : n ≤ N := by omega
      rw [raiseAtom_step previous] at path
      exact ih previous (.unpad path)

private theorem richCodeOrigin
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RichApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      ∃ annotation : RichApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset annotation.worlds worlds ∧
      ∀ policy, origin.headDepth policy ≤ incomingDepth policy := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, annotation, ⟨path⟩, included, sponsored, depth⟩ := origins a ha
  exact ⟨origin, annotation, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, sponsored, depth⟩

mutual
theorem WorldObsProvenance.applicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RichApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortable location origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored,
      fun policy => by simpa only [RichApplicationOrigin.headDepth, RichAppOrigin.ofSortable, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, _, _, .code source, location =>
    try simp only [RichObs.headDepth]
    exact source.applicationOrigin location member
  | _, _, _, _, .app hu hv domain codomain function argumentNode result,
      .app _ _ fn argument arguments admitted, .app _ _ fnProvenance argProvenance _ _, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    let origin : RichAppOrigin root env registry target source locals σ f arg :=
      ⟨_, _, _, _, hu, hv, _, _, _, _, _, location, _, _, _, _, _, fn, _, argument, arguments, admitted⟩
    exact ⟨.original origin, .original ⟨fnProvenance, argProvenance⟩, ⟨.refl⟩, fun _ h => h, fun _ h => h, fun policy => by simp only [origin]; exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichObs.headDepth]
    exact source.applicationOrigin (path.locate location) member
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichObs.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, _, _, .unpad source, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, children, ⟨.unpad path⟩, included, sponsored, depth⟩
  | _, _, _, _, _, _, .view source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path (.view change)⟩, included, sponsored, depth⟩
  | _, _, _, _, _, _, .select source selected, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    exact source.applicationOrigin location selected
  | _, _, _, _, _, _, .action source change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, children, ⟨.action path change⟩, included, sponsored, depth⟩
  | _, _, _, _, _, _, .castProfile equal child, location =>
    try simp only [RichObs.headDepth]
    have selected := member
    rw [← equal] at selected
    obtain ⟨origin, children, path, included, sponsored, depth⟩ :=
      child.applicationOrigin location selected
    refine ⟨origin, children, path, included, sponsored, ?_⟩
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
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := child.applicationOrigin location high
    exact ⟨origin, children, ⟨GeneralOutputPath.lowerRaised bound path⟩, included, sponsored,
      fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩

termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldCertProvenance.applicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint}
    (annotation : WorldCertProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      ∃ children : RichApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, origin.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy _ child, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨origin, children, path, included, sponsored, depth⟩ := child.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortable location origin),
      .original ⟨.legacy origin.function children.function, .legacy origin.argument children.argument⟩,
      path, included, sponsored,
      fun policy => by simpa only [RichApplicationOrigin.headDepth, RichAppOrigin.ofSortable, RichObs.headDepth] using depth policy⟩
  | _, _, _, _, node, .recipe code, .recipe child, location =>
    let origin : RichChargedAppOrigin root env registry target source locals σ f arg :=
      ⟨_, node, location, _, _, atom, _, .action (.select member) code⟩
    exact ⟨.charged origin, .charged (.action (.select member) child),
      ⟨.refl⟩, (fun _ h => h), (fun _ h => h), fun policy => by
        simp only [RichApplicationOrigin.headDepth, RichCert.headDepth, origin, RichCodeRecipe.headDepth]
        exact Nat.le_refl _⟩
  | _, _, _, _, _, _, .observe source _, location =>
    try simp only [RichCert.headDepth]
    exact source.applicationOrigin location member
  | _, _, _, _, _, _, .route path source, location =>
    try simp only [RichCert.headDepth]
    exact source.applicationOrigin (path.locate location) member
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichCert.headDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := left.applicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_left _ (included h),
        fun _ h => List.mem_append_left _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, children, path, included, sponsored, depth⟩ := right.applicationOrigin location h
      exact ⟨origin, children, path, fun _ h => List.mem_append_right _ (included h),
        fun _ h => List.mem_append_right _ (sponsored h),
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad source, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ := source.applicationOrigin location ha
    exact ⟨origin, children, ⟨.pad path⟩, included, sponsored, depth⟩
  | _, _, _, _, _, _, .down (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact richCodeOrigin .down value.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, _, .map view (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact richCodeOrigin (.map view) value.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, _, .support action (certificate := value) source, location =>
    try simp only [RichCert.headDepth]
    exact richCodeOrigin (.support action) value.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, _, .select (certificate := value) source selected, location =>
    try simp only [RichCert.headDepth]
    exact richCodeOrigin (.select selected) value.formed (fun _ h => source.applicationOrigin location h) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource