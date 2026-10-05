import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiCursor

/-! Joint executable legacy selection: syntax and its annotation are chosen
in one traversal. Every retained body has an honest original-input budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure WorldLegacyPiSelection (env : VEnv) {strata : EquationStratification env}
    (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (sizeBudget : Nat) (key : Key n) (result : Profile n) where
  rank : Nat
  table : List (Key rank × Profile rank)
  relevant : Bool
  pending : RankedPendingNativeRow env U registry target table relevant key result
  row : LegacyStoredPiRow env U registry target locals σ A B available relevant pending.oldKey pending.oldResult
  domainAnnotation : WorldSortableCertProvenance strata row.domain
  bodyAnnotation : WorldSortableCertProvenance strata row.body.certificate
  smaller : row.body.programSize < sizeBudget
  domainWorlds : domainAnnotation.worlds ⊆ budget.worlds
  bodyWorlds : bodyAnnotation.worlds ⊆ budget.worlds
  domainDepth : ∀ policy, row.domain.headDepth policy ≤ budget.depth policy
  bodyDepth : ∀ policy, row.body.certificate.headDepth policy ≤ budget.depth policy

abbrev WorldLegacyPiInputs (env : VEnv) {strata : EquationStratification env}
    (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (sizeBudget : Nat) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, ∀ {m : Nat} {domain body : VExpr} {support : Profile m}
    {rows : List (Key m × Profile m)} {key : Key m} {result : Profile m},
    GeneralOutputPath env U registry target atom (show Atom (m+1) from .pi domain body support rows) →
    (key, result) ∈ rows →
    Nonempty (WorldLegacyPiSelection env budget U registry target locals σ A B available sizeBudget key result)

private def appendPath {r s : Nat} {a : Atom r} {b : Atom s}
    (first : GeneralOutputPath env U registry target a b) :
    {n : Nat} → {c : Atom n} → GeneralOutputPath env U registry target b c →
      GeneralOutputPath env U registry target a c
  | _, _, .refl => first
  | _, _, .action path change => .action (appendPath first path) change
  | _, _, .code path change formed => .code (appendPath first path) change formed
  | _ + 1, .pad _, .pad path => .pad (appendPath first path)
  | _, _, .unpad path => .unpad (appendPath first path)

private theorem WorldLegacyPiInputs.code
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget p) :
    WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget q := by
  intro atom member m domain body support rows key result path selected
  obtain ⟨old, present, ⟨step⟩⟩ := action.atom member
  exact origins old present (appendPath (.code .refl step (formed.singleton_of_mem present)) path) selected

mutual
theorem WorldLegacyObsProvenance.selectPiProgram
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {observation : Obs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyObsProvenance strata observation)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf observation ≤ sizeBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, observation.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget profile := by
  match annotation with
  | .empty =>
    simp only [Obs.headDepth] at depth
    exact fun _ member => nomatch member
  | .pi domain guard rows domainAnnotation rowsAnnotation =>
    simp only [Obs.headDepth] at depth
    intro atom member m nextDomain nextBody support table key result path selected
    cases List.mem_singleton.mp member
    obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result selected
    obtain ⟨row, bodyAnnotation, ambientEq, footprintEq, same, smaller, bodyWorlds, bodyDepth⟩ :=
      rowsAnnotation.storedCursor domain
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun i need hm => resources i need (List.mem_append_right _ hm)) pending.member
    obtain ⟨domAnn, domWorlds, domDepth⟩ :
        ∃ domAnn : WorldSortableCertProvenance strata row.domain,
          domAnn.worlds ⊆ budget.worlds ∧
          ∀ policy, row.domain.headDepth policy ≤ budget.depth policy := by
      cases row
      dsimp only at ambientEq footprintEq same ⊢
      cases ambientEq
      cases footprintEq
      cases same
      refine ⟨.ofCode domain domain.formed domainAnnotation, fun _ present => worlds (List.mem_append_left _ present), ?_⟩
      intro policy
      simpa only [SortableCert.headDepth] using Nat.le_trans (Nat.le_max_left _ _) (depth policy)
    refine ⟨⟨_, _, _, pending, row, domAnn, bodyAnnotation, ?_, domWorlds,
      fun _ present => worlds (List.mem_append_right _ (bodyWorlds present)), domDepth, ?_⟩⟩
    · apply Nat.lt_of_lt_of_le ?_ bounded
      simp_wf
      omega
    · intro policy
      exact Nat.le_trans (bodyDepth policy) (Nat.le_trans (Nat.le_max_right _ _) (depth policy))
  | .union left right leftAnnotation rightAnnotation =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path selected
    · exact rightAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path selected
  | .view query change child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    cases List.mem_singleton.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (.view change)) path) selected
  | .pad query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth old present (appendPath (.pad .refl) path) selected
  | .unpad query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth (.pad atom) (List.mem_map_of_mem member)
      (appendPath (.unpad .refl) path) selected
  | .rowShift query child =>
    simp only [Obs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    cases List.mem_singleton.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action (.pad .refl) (.view (.commutePadFn _ _))) path) selected
termination_by sizeOf annotation

theorem WorldLegacyCertProvenance.selectPiProgram
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyCertProvenance strata certificate)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf certificate ≤ sizeBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, certificate.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget profile := by
  match annotation with
  | .seed query _ child =>
    simp only [CodeCert.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [CodeCert.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path selected
    · exact rightAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path selected
  | .pad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .pad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .familyPad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .familyPad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .unpad query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .unpad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .down query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .down query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .map change query child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.map change) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .select query member child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.select member) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .focusMinimal query minimal bound child =>
    simp only [CodeCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.focusMinimal minimal bound) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
termination_by sizeOf annotation

theorem WorldSortableObsProvenance.selectPiProgram
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldSortableObsProvenance strata observation)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf observation ≤ sizeBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, observation.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget profile := by
  match annotation with
  | .legacy query child =>
    simp only [SortableObs.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .code _ query child =>
    simp only [SortableObs.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path selected
    · exact rightAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path selected
  | .view query change child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    cases List.mem_singleton.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (.view change)) path) selected
  | .action query change child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    cases List.mem_singleton.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action .refl (change)) path) selected
  | .pad query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth old present (appendPath (.pad .refl) path) selected
  | .unpad query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth (.pad atom) (List.mem_map_of_mem member)
      (appendPath (.unpad .refl) path) selected
  | .rowShift query child =>
    simp only [SortableObs.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    cases List.mem_singleton.mp member
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth _ (List.mem_singleton_self _)
      (appendPath (.action (.pad .refl) (.view (.commutePadFn _ _))) path) selected
termination_by sizeOf annotation

theorem WorldSortableCertProvenance.selectPiProgram
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
    (annotation : WorldSortableCertProvenance strata certificate)
    (resources : footprint.Available available) (sizeBudget : Nat) (bounded : sizeOf certificate ≤ sizeBudget)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, certificate.headDepth policy ≤ budget.depth policy) :
    WorldLegacyPiInputs env budget U registry target locals σ A B available sizeBudget profile := by
  match annotation with
  | .pi domain guard rows domainAnnotation rowsAnnotation =>
    simp only [SortableCert.headDepth] at depth
    intro atom member m nextDomain nextBody support table key result path selected
    cases List.mem_singleton.mp member
    obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result selected
    obtain ⟨row, bodyAnnotation, ambientEq, footprintEq, same, smaller, bodyWorlds, bodyDepth⟩ :=
      rowsAnnotation.storedCursor domain
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun i need hm => resources i need (List.mem_append_right _ hm)) pending.member
    obtain ⟨domAnn, domWorlds, domDepth⟩ :
        ∃ domAnn : WorldSortableCertProvenance strata row.domain,
          domAnn.worlds ⊆ budget.worlds ∧
          ∀ policy, row.domain.headDepth policy ≤ budget.depth policy := by
      cases row
      dsimp only at ambientEq footprintEq same ⊢
      cases ambientEq
      cases footprintEq
      cases same
      refine ⟨domainAnnotation, fun _ present => worlds (List.mem_append_left _ present), ?_⟩
      intro policy
      simpa only [SortableCert.headDepth] using Nat.le_trans (Nat.le_max_left _ _) (depth policy)
    refine ⟨⟨_, _, _, pending, row, domAnn, bodyAnnotation, ?_, domWorlds,
      fun _ present => worlds (List.mem_append_right _ (bodyWorlds present)), domDepth, ?_⟩⟩
    · apply Nat.lt_of_lt_of_le ?_ bounded
      simp_wf
      omega
    · intro policy
      exact Nat.le_trans (bodyDepth policy) (Nat.le_trans (Nat.le_max_right _ _) (depth policy))
  | .ofCode query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .observe query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .seed query _ child =>
    simp only [SortableCert.headDepth] at depth
    exact child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth
  | .union left right leftAnnotation rightAnnotation =>
    simp only [SortableCert.headDepth] at depth
    intro atom member m domain body support rows key result path selected
    rcases List.mem_append.mp member with member | member
    · exact leftAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_left _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_left _ present)) (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member path selected
    · exact rightAnnotation.selectPiProgram (fun i need hm => resources i need (List.mem_append_right _ hm)) sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (fun _ present => worlds (List.mem_append_right _ present)) (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member path selected
  | .pad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .pad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .familyPad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .familyPad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .unpad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .unpad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .down query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .down query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .map change query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.map change) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .select query member child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.select member) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .focusMinimal query minimal bound child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.focusMinimal minimal bound) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .sortPad query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code .sortPad query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
  | .support action query child =>
    simp only [SortableCert.headDepth] at depth
    exact WorldLegacyPiInputs.code (.support action) query.formed (child.selectPiProgram resources sizeBudget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) worlds depth)
termination_by sizeOf annotation

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
