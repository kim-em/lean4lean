import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiSizedCursor

/-! Legacy Pi leaf selection does not require a row. In particular, domain
elimination of a Pi with an empty table retains its literal original domain
and complete annotated row program, with the output path still pending. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

inductive WorldLegacyPiLeafProvenance (strata : EquationStratification env) :
    {n : Nat} → {atom : Atom n} →
    LegacyPiLeaf env U registry target locals σ A B available atom → Type where
  | plain {domain : CodeCert env U registry target locals σ A ambient domainFootprint}
      {rows : PiRows env U registry target locals σ A B ambient table rowFootprint}
      {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
      {resources : (domainFootprint ++ rowFootprint).Available available}
      (domainAnnotation : WorldLegacyCertProvenance strata domain)
      (rowsAnnotation : WorldLegacyRowsProvenance strata rows) :
      WorldLegacyPiLeafProvenance strata (.plain domain guard rows resources)
  | sortable {domain : SortableCert env U registry target locals σ A true ambient domainFootprint}
      {rows : SortableRows env U registry target locals σ A B relevant ambient table rowFootprint}
      {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
      {resources : (domainFootprint ++ rowFootprint).Available available}
      (domainAnnotation : WorldSortableCertProvenance strata domain)
      (rowsAnnotation : WorldSortableRowsProvenance strata rows) :
      WorldLegacyPiLeafProvenance strata (.sortable domain guard rows resources)

noncomputable def WorldLegacyPiLeafProvenance.worlds
    {n : Nat} {atom : Atom n}
    {leaf : LegacyPiLeaf env U registry target locals σ A B available atom}
    (annotation : WorldLegacyPiLeafProvenance strata leaf) : List (World strata.rules.length) :=
  match n, atom, leaf, annotation with
  | _ + 1, .pi _ _ _ _, _, .plain domain rows => domain.worlds ++ rows.worlds
  | _ + 1, .pi _ _ _ _, _, .sortable domain rows => domain.worlds ++ rows.worlds

noncomputable def WorldLegacyPiLeafProvenance.retainedSize
    {n : Nat} {atom : Atom n}
    {leaf : LegacyPiLeaf env U registry target locals σ A B available atom}
    (annotation : WorldLegacyPiLeafProvenance strata leaf) : Nat :=
  match n, atom, leaf, annotation with
  | _ + 1, .pi _ _ _ _, _, .plain domain rows => max (sizeOf domain) (sizeOf rows)
  | _ + 1, .pi _ _ _ _, _, .sortable domain rows => max (sizeOf domain) (sizeOf rows)

noncomputable def LegacyPiLeaf.headDepth
    {n : Nat} {atom : Atom n}
    (leaf : LegacyPiLeaf env U registry target locals σ A B available atom)
    (policy : Name → Nat → Nat) : Nat :=
  match n, atom, leaf with
  | _ + 1, .pi _ _ _ _, .plain domain _ rows _ => max (domain.headDepth policy) (rows.headDepth policy)
  | _ + 1, .pi _ _ _ _, .sortable domain _ rows _ => max (domain.headDepth policy) (rows.headDepth policy)

structure WorldLegacyPiLeafSelection (env : VEnv) {strata : EquationStratification env}
    (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (sizeBudget annotationBudget : Nat) (atom : Atom n) where
  origin : LegacyPiOrigin env U registry target locals σ A B available sizeBudget atom
  annotation : WorldLegacyPiLeafProvenance strata origin.leaf
  worlds : annotation.worlds ⊆ budget.worlds
  smaller : annotation.retainedSize < annotationBudget
  depth : ∀ policy, origin.leaf.headDepth policy ≤ budget.depth policy

abbrev WorldLegacyPiLeafInputs (env : VEnv) {strata : EquationStratification env}
    (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (sizeBudget annotationBudget : Nat) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, ∀ {m : Nat} {domain body : VExpr} {support : Profile m}
    {rows : List (Key m × Profile m)},
    GeneralOutputPath env U registry target atom (show Atom (m+1) from .pi domain body support rows) →
    Nonempty (WorldLegacyPiLeafSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget (show Atom (m+1) from .pi domain body support rows))

private def appendPath {r s : Nat} {a : Atom r} {b : Atom s}
    (first : GeneralOutputPath env U registry target a b) :
    {n : Nat} → {c : Atom n} → GeneralOutputPath env U registry target b c →
      GeneralOutputPath env U registry target a c
  | _, _, .refl => first
  | _, _, .action path change => .action (appendPath first path) change
  | _, _, .code path change formed => .code (appendPath first path) change formed
  | _ + 1, .pad _, .pad path => .pad (appendPath first path)
  | _, _, .unpad path => .unpad (appendPath first path)

private theorem WorldLegacyPiLeafInputs.code
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget p) :
    WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget q := by
  intro atom member m domain body support rows path
  obtain ⟨old, present, ⟨step⟩⟩ := action.atom member
  exact origins old present (appendPath (.code .refl step (formed.singleton_of_mem present)) path)

mutual
theorem WorldLegacyObsProvenance.selectPiLeafSized
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {observation : Obs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyObsProvenance strata observation)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf observation ≤ sizeBudget)
    (annotationBudget : Nat) (annotationBound : sizeOf annotation ≤ annotationBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, observation.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget profile := by
  match annotation with
  | .empty =>
    simp only [Obs.headDepth] at depth
    exact fun _ member => nomatch member
  | .pi domain guard rows domainAnnotation rowsAnnotation =>
    simp only [Obs.headDepth] at depth
    intro atom member m nextDomain nextBody support table path
    cases List.mem_singleton.mp member
    let leaf : LegacyPiLeaf env U registry target locals σ A B available _ :=
      .plain domain guard rows resources
    let selected : WorldLegacyPiLeafProvenance strata leaf := .plain domainAnnotation rowsAnnotation
    refine ⟨{
      origin := ⟨_, _, leaf, path, by simpa only [leaf, LegacyPiLeaf.programSize] using bounded⟩
      annotation := selected
      worlds := ?_
      smaller := ?_
      depth := ?_ }⟩
    · change (domainAnnotation.worlds ++ rowsAnnotation.worlds) ⊆ budget.worlds
      exact worlds
    · change max (sizeOf domainAnnotation) (sizeOf rowsAnnotation) < annotationBudget
      apply Nat.lt_of_lt_of_le _ annotationBound
      simp_wf
      omega
    · change ∀ policy, max (domain.headDepth policy) (rows.headDepth policy) ≤ budget.depth policy
      exact depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows path
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path
    · exact rightAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path
  | .view query change child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows path
    cases List.mem_singleton.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (.view change)) path)
  | .pad query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows path
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth old present (appendPath (.pad .refl) path)
  | .unpad query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows path
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth (.pad atom) (List.mem_map_of_mem member)
      (appendPath (.unpad .refl) path)
  | .rowShift query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows path
    cases List.mem_singleton.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action (.pad .refl) (.view (.commutePadFn _ _))) path)
termination_by sizeOf annotation

theorem WorldLegacyCertProvenance.selectPiLeafSized
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyCertProvenance strata certificate)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf certificate ≤ sizeBudget)
    (annotationBudget : Nat) (annotationBound : sizeOf annotation ≤ annotationBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, certificate.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget profile := by
  match annotation with
  | .seed query _ child =>
    simp only [CodeCert.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [CodeCert.headDepth] at depth
    intro atom member m domain body support rows path
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path
    · exact rightAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path
  | .pad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .pad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .familyPad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .familyPad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .unpad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .unpad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .down query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .down query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .map change query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.map change) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .select query member child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.select member) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .focusMinimal query minimal bound child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.focusMinimal minimal bound) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
termination_by sizeOf annotation

theorem WorldSortableObsProvenance.selectPiLeafSized
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldSortableObsProvenance strata observation)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf observation ≤ sizeBudget)
    (annotationBudget : Nat) (annotationBound : sizeOf annotation ≤ annotationBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, observation.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget profile := by
  match annotation with
  | .legacy query child =>
    simp only [SortableObs.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .code _ query child =>
    simp only [SortableObs.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path
    · exact rightAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path
  | .view query change child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    cases List.mem_singleton.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (.view change)) path)
  | .action query change child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    cases List.mem_singleton.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (change)) path)
  | .pad query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth old present (appendPath (.pad .refl) path)
  | .unpad query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth (.pad atom) (List.mem_map_of_mem member)
      (appendPath (.unpad .refl) path)
  | .rowShift query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows path
    cases List.mem_singleton.mp member
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action (.pad .refl) (.view (.commutePadFn _ _))) path)
termination_by sizeOf annotation

theorem WorldSortableCertProvenance.selectPiLeafSized
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
    (annotation : WorldSortableCertProvenance strata certificate)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf certificate ≤ sizeBudget)
    (annotationBudget : Nat) (annotationBound : sizeOf annotation ≤ annotationBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, certificate.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiLeafInputs env budget U registry target locals σ A B available sizeBudget annotationBudget profile := by
  match annotation with
  | .pi domain guard rows domainAnnotation rowsAnnotation =>
    simp only [SortableCert.headDepth] at depth
    intro atom member m nextDomain nextBody support table path
    cases List.mem_singleton.mp member
    let leaf : LegacyPiLeaf env U registry target locals σ A B available _ :=
      .sortable domain guard rows resources
    let selected : WorldLegacyPiLeafProvenance strata leaf := .sortable domainAnnotation rowsAnnotation
    refine ⟨{
      origin := ⟨_, _, leaf, path, by simpa only [leaf, LegacyPiLeaf.programSize] using bounded⟩
      annotation := selected
      worlds := ?_
      smaller := ?_
      depth := ?_ }⟩
    · change (domainAnnotation.worlds ++ rowsAnnotation.worlds) ⊆ budget.worlds
      exact worlds
    · change max (sizeOf domainAnnotation) (sizeOf rowsAnnotation) < annotationBudget
      apply Nat.lt_of_lt_of_le _ annotationBound
      simp_wf
      omega
    · change ∀ policy, max (domain.headDepth policy) (rows.headDepth policy) ≤ budget.depth policy
      exact depth
  | .ofCode query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .observe query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .seed query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [SortableCert.headDepth] at depth
    intro atom member m domain body support rows path
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path
    · exact rightAnnotation.selectPiLeafSized (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path
  | .pad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .pad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .familyPad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .familyPad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .unpad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .unpad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .down query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .down query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .map change query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.map change) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .select query member child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.select member) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .focusMinimal query minimal bound child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.focusMinimal minimal bound) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .sortPad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code .sortPad query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
  | .support action query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiLeafInputs.code (.support action) query.formed (child.selectPiLeafSized resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) annotationBudget (by apply Nat.le_trans ?_ annotationBound; simp_wf <;> omega) worlds depth)
termination_by sizeOf annotation

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
