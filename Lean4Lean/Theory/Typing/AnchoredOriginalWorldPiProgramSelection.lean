import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiProgramCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

/-! Joint Pi program selection retains literal native/legacy/charged programs,
exact annotations, and the original native prefix. Annotation descent is strict;
pending output paths do not allocate replacement recursive inputs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private GeneralOutputPath.lowerRaised from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

inductive WorldPiProgramLeafProvenance (strata : EquationStratification env) :
    {n : Nat} → {atom : Atom n} →
    RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom → Type where
  | native
      {domainNode : EndpointState sourceEnv U source A (.sort u)}
      {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
      {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table rowFootprint}
      {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
      (domainAnnotation : WorldCertProvenance strata domain)
      (rowsAnnotation : WorldRowsProvenance strata rows) :
      WorldPiProgramLeafProvenance strata (.native hu hv domain guard rows resources)
  | legacyCode {certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
      (child : WorldSortableCertProvenance strata certificate) :
      WorldPiProgramLeafProvenance strata (.legacyCode certificate resources member)
  | legacyObs {observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint}
      (child : WorldSortableObsProvenance strata observation) :
      WorldPiProgramLeafProvenance strata (.legacyObs observation resources member)
  | recipe {code : RichCodeRecipe env U registry target source locals σ (.forallE A B) relevant profile footprint}
      (child : WorldCodeRecipeProvenance strata code) :
      WorldPiProgramLeafProvenance strata (.recipe code resources member)

noncomputable def WorldPiProgramLeafProvenance.worlds
    {n : Nat} {atom : Atom n}
    {leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom}
    (annotation : WorldPiProgramLeafProvenance strata leaf) : List (EquationWorldClosureOrder.World strata.rules.length) :=
  match n, atom, leaf, annotation with
  | _ + 1, .pi _ _ _ _, _, .native domain rows => domain.worlds ++ rows.worlds
  | _, _, _, .legacyCode child => child.worlds
  | _, _, _, .legacyObs child => child.worlds
  | _, _, _, .recipe child => child.worlds

noncomputable def WorldPiProgramLeafProvenance.retainedSize
    {n : Nat} {atom : Atom n}
    {leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom}
    (annotation : WorldPiProgramLeafProvenance strata leaf) : Nat :=
  match n, atom, leaf, annotation with
  | _ + 1, .pi _ _ _ _, _, .native domain rows => max (sizeOf domain) (sizeOf rows)
  | _, _, _, .legacyCode child => sizeOf child
  | _, _, _, .legacyObs child => sizeOf child
  | _, _, _, .recipe child => sizeOf child

noncomputable def RichPiProgramLeaf.headDepth
    {n : Nat} {atom : Atom n}
    (leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom)
    (policy : Name → Nat → Nat) : Nat :=
  match n, atom, leaf with
  | _ + 1, .pi _ _ _ _, .native _ _ domain _ rows _ => max (domain.headDepth policy) (rows.headDepth policy)
  | _, _, .legacyCode certificate _ _ => certificate.headDepth policy
  | _, _, .legacyObs observation _ _ => observation.headDepth policy
  | _, _, .recipe code _ _ => code.headDepth policy

def RichPiProgramLeaf.RootedAt
    {n : Nat} {atom : Atom n}
    (leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom)
    (start : EndpointState sourceEnv U source (.forallE A B) assigned) : Prop :=
  match n, atom, leaf with
  | _ + 1, .pi _ _ _ _, .native (domainNode := domain) (bodyNode := body) hu hv _ _ _ _ =>
    Nonempty (PrefixRoute sourceEnv U source (.forallE A B) start (.pi hu hv domain body))
  | _, _, .legacyCode .. | _, _, .legacyObs .. | _, _, .recipe .. => True

theorem RichPiProgramLeaf.RootedAt.prepend
    {leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom}
    (rooted : leaf.RootedAt middle)
    (path : PrefixRoute sourceEnv U source (.forallE A B) start middle) : leaf.RootedAt start := by
  cases leaf with
  | native hu hv domain guard rows resources =>
    obtain ⟨route⟩ := rooted
    exact ⟨path.append route⟩
  | legacyCode | legacyObs | recipe => simp only [RichPiProgramLeaf.RootedAt]

private theorem codeOrigin
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {incomingDepth : (Name → Nat → Nat) → Nat}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms,
      ∃ syntaxBudget, ∃ origin : RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available syntaxBudget a,
      ∃ child : WorldPiProgramLeafProvenance strata origin.leaf,
        child.worlds ⊆ worlds ∧ origin.leaf.RootedAt node ∧ child.retainedSize < budget ∧
        ∀ policy, origin.leaf.headDepth policy ≤ incomingDepth policy)
    (member : b ∈ q.atoms) :
    ∃ syntaxBudget, ∃ origin : RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available syntaxBudget b,
    ∃ child : WorldPiProgramLeafProvenance strata origin.leaf,
      child.worlds ⊆ worlds ∧ origin.leaf.RootedAt node ∧ child.retainedSize < budget ∧
      ∀ policy, origin.leaf.headDepth policy ≤ incomingDepth policy := by
  obtain ⟨a, present, ⟨step⟩⟩ := action.atom member
  obtain ⟨syntaxBudget, origin, child, included, rooted, smaller, depth⟩ := origins a present
  exact ⟨syntaxBudget, { origin with path := .code origin.path step (formed.singleton_of_mem present) },
    child, included, rooted, smaller, depth⟩

mutual
theorem WorldObsProvenance.piProgramSelection
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {profile : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (resources : footprint.Available available)
    (member : atom ∈ profile.atoms)
    {budget : Nat}
    (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ syntaxBudget, ∃ origin : RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available syntaxBudget atom,
    ∃ child : WorldPiProgramLeafProvenance strata origin.leaf,
      child.worlds ⊆ annotation.worlds ∧ origin.leaf.RootedAt node ∧ child.retainedSize < budget ∧
      ∀ policy, origin.leaf.headDepth policy ≤ query.headDepth policy := by
  match n, profile, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy value child, location =>
    try simp only [RichObs.headDepth]
    refine ⟨_, ⟨_, atom, .legacyObs value resources member, .refl, Nat.le_refl _⟩,
      .legacyObs child, (fun _ h => by simp only [WorldPiProgramLeafProvenance.worlds] at h; exact h), (by simp only [RichPiProgramLeaf.RootedAt]), ?_, (fun _ => by simp only [RichPiProgramLeaf.headDepth]; exact Nat.le_refl _)⟩
    simp only [WorldPiProgramLeafProvenance.retainedSize]
    simp +zetaDelta at sizeBound
    omega
  | _, _, _, _, _, _, .empty, location => cases member
  | _, _, _, _, _, _, .code child, location =>
    try simp only [RichObs.headDepth]
    exact child.piProgramSelection (budget := budget) location resources member
  | _, _, _, _, _, _, .route path child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) (path.locate location) resources member
    exact ⟨syntaxBudget, origin, selected, included, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichObs.headDepth]
    rcases List.mem_append.mp member with present | present
    · obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
        left.piProgramSelection (budget := budget) location
          (fun i need hm => resources i need (List.mem_append_left _ hm)) present
      exact ⟨syntaxBudget, origin, selected, (fun _ hm => List.mem_append_left _ (included hm)), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
        right.piProgramSelection (budget := budget) location
          (fun i need hm => resources i need (List.mem_append_right _ hm)) present
      exact ⟨syntaxBudget, origin, selected, (fun _ hm => List.mem_append_right _ (included hm)), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨a, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources present
    exact ⟨syntaxBudget, { origin with path := .pad origin.path }, selected, included, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .unpad child, location =>
    try simp only [RichObs.headDepth]
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources
        (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨syntaxBudget, { origin with path := .unpad origin.path }, selected, included, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .action child change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources
        (List.mem_singleton_self _)
    exact ⟨syntaxBudget, { origin with path := .action origin.path change }, selected, included, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .view child change, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources
        (List.mem_singleton_self _)
    exact ⟨syntaxBudget, { origin with path := .action origin.path (.view change) }, selected, included, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .select child present, location =>
    try simp only [RichObs.headDepth]
    cases List.mem_singleton.mp member
    exact child.piProgramSelection (budget := budget) location resources present
  | _, _, _, _, _, _, .castProfile equal child, location =>
    try simp only [RichObs.headDepth]
    have present := member
    rw [← equal] at present
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources present
    refine ⟨syntaxBudget, origin, selected, included, rooted, smaller, ?_⟩
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
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources high
    exact ⟨syntaxBudget, { origin with path := GeneralOutputPath.lowerRaised bound origin.path }, selected,
      included, rooted, smaller,
      fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldCertProvenance.piProgramSelection
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {profile : Profile n}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (annotation : WorldCertProvenance strata query)
    (location : Located root node) (resources : footprint.Available available)
    (member : atom ∈ profile.atoms)
    {budget : Nat}
    (sizeBound : sizeOf annotation ≤ budget := by
      try simp_all +zetaDelta
      try rw [WorldObsProvenance.castProfile.sizeOf_spec] at *
      omega) :
    ∃ syntaxBudget, ∃ origin : RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available syntaxBudget atom,
    ∃ child : WorldPiProgramLeafProvenance strata origin.leaf,
      child.worlds ⊆ annotation.worlds ∧ origin.leaf.RootedAt node ∧ child.retainedSize < budget ∧
      ∀ policy, origin.leaf.headDepth policy ≤ query.headDepth policy := by
  match n, profile, footprint, assigned, node, query, annotation, location with
  | _, _, _, _, _, _, .legacy value child, location =>
    try simp only [RichCert.headDepth]
    refine ⟨_, ⟨_, atom, .legacyCode value resources member, .refl, Nat.le_refl _⟩,
      .legacyCode child, (fun _ h => by simp only [WorldPiProgramLeafProvenance.worlds] at h; exact h), (by simp only [RichPiProgramLeaf.RootedAt]), ?_, (fun _ => by simp only [RichPiProgramLeaf.headDepth]; exact Nat.le_refl _)⟩
    simp only [WorldPiProgramLeafProvenance.retainedSize]
    simp +zetaDelta at sizeBound
    omega
  | _, _, _, _, _, .recipe code, .recipe child, location =>
    try simp only [RichCert.headDepth]
    refine ⟨_, ⟨_, atom, .recipe code resources member, .refl, Nat.le_refl _⟩,
      .recipe child, (fun _ h => by simp only [WorldPiProgramLeafProvenance.worlds] at h; exact h), (by simp only [RichPiProgramLeaf.RootedAt]), ?_, (fun _ => by simp only [RichPiProgramLeaf.headDepth]; exact Nat.le_refl _)⟩
    simp only [WorldPiProgramLeafProvenance.retainedSize]
    simp +zetaDelta at sizeBound
    omega
  | _, _, _, _, _, _, .observe child _, location =>
    try simp only [RichCert.headDepth]
    exact child.piProgramSelection (budget := budget) location resources member
  | _, _, _, _, .pi hu hv domainNode bodyNode, _, .pi _ _ domain guard rows domainAnnotation rowsAnnotation, location =>
    try simp only [RichCert.headDepth]
    cases List.mem_singleton.mp member
    refine ⟨_, ⟨_, _, .native hu hv domain guard rows resources, .refl, Nat.le_refl _⟩,
      .native domainAnnotation rowsAnnotation, (fun _ h => by simp only [WorldPiProgramLeafProvenance.worlds] at h; exact h), ⟨.done _⟩, ?_, (fun _ => by simp only [RichPiProgramLeaf.headDepth]; exact Nat.le_refl _)⟩
    simp only [WorldPiProgramLeafProvenance.retainedSize]
    simp +zetaDelta at sizeBound
    omega
  | _, _, _, _, _, _, .route path child, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) (path.locate location) resources member
    exact ⟨syntaxBudget, origin, selected, included, rooted.prepend path, smaller, depth⟩
  | _, _, _, _, _, _, .union left right, location =>
    try simp only [RichCert.headDepth]
    rcases List.mem_append.mp member with present | present
    · obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
        left.piProgramSelection (budget := budget) location
          (fun i need hm => resources i need (List.mem_append_left _ hm)) present
      exact ⟨syntaxBudget, origin, selected, (fun _ hm => List.mem_append_left _ (included hm)), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
        right.piProgramSelection (budget := budget) location
          (fun i need hm => resources i need (List.mem_append_right _ hm)) present
      exact ⟨syntaxBudget, origin, selected, (fun _ hm => List.mem_append_right _ (included hm)), rooted, smaller,
        fun policy => Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | _, _, _, _, _, _, .pad child, location =>
    try simp only [RichCert.headDepth]
    obtain ⟨a, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨syntaxBudget, origin, selected, included, rooted, smaller, depth⟩ :=
      child.piProgramSelection (budget := budget) location resources present
    exact ⟨syntaxBudget, { origin with path := .pad origin.path }, selected, included, rooted, smaller, depth⟩
  | _, _, _, _, _, _, .down (certificate := value) child, location =>
    try simp only [RichCert.headDepth]
    exact codeOrigin .down value.formed
      (fun _ present => child.piProgramSelection (budget := budget)
        location resources present) member
  | _, _, _, _, _, _, .map view (certificate := value) child, location =>
    try simp only [RichCert.headDepth]
    exact codeOrigin (.map view) value.formed
      (fun _ present => child.piProgramSelection (budget := budget)
        location resources present) member
  | _, _, _, _, _, _, .support action (certificate := value) child, location =>
    try simp only [RichCert.headDepth]
    exact codeOrigin (.support action) value.formed
      (fun _ present => child.piProgramSelection (budget := budget)
        location resources present) member
  | _, _, _, _, _, _, .select (certificate := value) child selected, location =>
    try simp only [RichCert.headDepth]
    exact codeOrigin (.select selected) value.formed
      (fun _ present => child.piProgramSelection (budget := budget)
        location resources present) member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
