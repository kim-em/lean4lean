import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private theorem codeOrigin_allDepth
    {limit : (Name → Bool) → Nat}
    (action : SortableCodeAction env U registry Γ relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output a) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ limit current))
    (member : b ∈ q.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output b) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ limit current) := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, ⟨path⟩, included, bounded⟩ := origins a ha
  exact ⟨origin, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, bounded⟩

mutual
theorem Obs.applicationOrigin_allDepth
    {demand : Profile n}
    (source : Obs env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ source.nativeDepth current) := by
  match n, demand, footprint, source with
  | _, _, _, .empty => cases member
  | _, _, _, .app fn argument arguments admitted =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, _, _, _, (.legacy fn), _, (.legacy argument), arguments.toGeneral, admitted⟩, ⟨.refl⟩, (fun _ h => h), by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .union left right =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, bounded⟩ := left.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, path, included, bounded⟩ := right.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_right _ _)⟩
  | _, _, _, .pad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth ha
    exact ⟨origin, ⟨.pad path⟩, included, bounded⟩
  | _, _, _, .unpad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, bounded⟩
  | _, _, _, .view source change =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included, bounded⟩
  | _, _, _, .rowShift source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included, bounded⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.applicationOrigin_allDepth
    {demand : Profile n}
    (source : CodeCert env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ source.nativeDepth current) := by
  match n, demand, footprint, source with
  | _, _, _, .seed source _ => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .union left right =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, bounded⟩ := left.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, path, included, bounded⟩ := right.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_right _ _)⟩
  | _, _, _, .pad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth ha
    exact ⟨origin, ⟨.pad path⟩, included, bounded⟩
  | _, _, _, .unpad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, bounded⟩
  | _, _, _, .familyPad source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) .familyPad source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .down source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) .down source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .map v source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.map v) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .select source selected => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.select selected) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .focusMinimal source minimal bound => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.focusMinimal minimal bound) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.applicationOrigin_allDepth
    {demand : Profile n}
    (source : SortableObs env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ source.nativeDepth current) := by
  match n, demand, footprint, source with
  | _, _, _, .legacy source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .code _ source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .app fn argument arguments admitted =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, _, _, _, fn, _, argument, arguments, admitted⟩, ⟨.refl⟩, (fun _ h => h), by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .union left right =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, bounded⟩ := left.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, path, included, bounded⟩ := right.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_right _ _)⟩
  | _, _, _, .pad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth ha
    exact ⟨origin, ⟨.pad path⟩, included, bounded⟩
  | _, _, _, .unpad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, bounded⟩
  | _, _, _, .view source change =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included, bounded⟩
  | _, _, _, .action source change =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path change⟩, included, bounded⟩
  | _, _, _, .rowShift source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included, bounded⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.applicationOrigin_allDepth
    {demand : Profile n}
    (source : SortableCert env U registry Γ locals σ (.app f arg) relevant demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      (∀ current, max (origin.function.nativeDepth current) (origin.argument.nativeDepth current) ≤ source.nativeDepth current) := by
  match n, demand, footprint, source with
  | _, _, _, .ofCode source _ => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .observe source _ => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .seed source _ => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using source.applicationOrigin_allDepth member
  | _, _, _, .union left right =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, bounded⟩ := left.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_left _ _)⟩
    · obtain ⟨origin, path, included, bounded⟩ := right.applicationOrigin_allDepth h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), by intro current; exact Nat.le_trans (bounded current) (Nat.le_max_right _ _)⟩
  | _, _, _, .pad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth ha
    exact ⟨origin, ⟨.pad path⟩, included, bounded⟩
  | _, _, _, .unpad source =>
    simp only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth]
    obtain ⟨origin, ⟨path⟩, included, bounded⟩ := source.applicationOrigin_allDepth (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, bounded⟩
  | _, _, _, .familyPad source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) .familyPad source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .down source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) .down source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .map v source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.map v) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .select source selected => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.select selected) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .focusMinimal source minimal bound => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.focusMinimal minimal bound) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .sortPad source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) .sortPad source.formed (fun _ h => source.applicationOrigin_allDepth h) member
  | _, _, _, .support action source => simpa only [Obs.nativeDepth, CodeCert.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth] using codeOrigin_allDepth (limit := source.nativeDepth) (.support action) source.formed (fun _ h => source.applicationOrigin_allDepth h) member
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted
