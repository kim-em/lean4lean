import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredSortableOutputPath

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive GeneralOutputPath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) {r : Nat} (source : Atom r) : {n : Nat} → Atom n → Type where
  | refl : GeneralOutputPath env U registry Γ source source
  | action (path : GeneralOutputPath env U registry Γ source a)
      (change : AtomAction env U registry Γ a b) : GeneralOutputPath env U registry Γ source b
  | code (path : GeneralOutputPath env U registry Γ source a)
      (change : SortableCodeAction env U registry Γ relevant (.singleton a) next (.singleton b))
      (formed : (Profile.singleton a).HasType (.sort relevant)) :
      GeneralOutputPath env U registry Γ source b
  | pad (path : GeneralOutputPath env U registry Γ source (a : Atom n)) :
      GeneralOutputPath env U registry Γ source (n := n + 1) (.pad a)
  | unpad (path : GeneralOutputPath env U registry Γ source (n := n + 1) (.pad (a : Atom n))) :
      GeneralOutputPath env U registry Γ source a

structure SortableAppOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  rank : Nat
  key : Key rank
  output : Atom rank
  functionFootprint : Footprint
  argumentFootprint : Footprint
  function : SortableObs env U registry Γ locals σ f (Profile.fn key output) functionFootprint
  rawInput : Profile rank
  argument : SortableObs env U registry Γ locals σ a rawInput argumentFootprint
  arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input
  admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)

private theorem codeOrigin
    (action : SortableCodeAction env U registry Γ relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output a) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint)
    (member : b ∈ q.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output b) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, ⟨path⟩, included⟩ := origins a ha
  exact ⟨origin, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included⟩

mutual
theorem Obs.applicationOrigin
    {demand : Profile n}
    (source : Obs env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  match n, demand, footprint, source with
  | _, _, _, .empty => cases member
  | _, _, _, .app fn argument arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, _, _, _, (.legacy fn), _, (.legacy argument), arguments.toGeneral, admitted⟩, ⟨.refl⟩, fun _ h => h⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included⟩
  | _, _, _, .rowShift source =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.applicationOrigin
    {demand : Profile n}
    (source : CodeCert env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  match n, demand, footprint, source with
  | _, _, _, .seed source _ => exact source.applicationOrigin member
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, .familyPad source => exact codeOrigin .familyPad source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .down source => exact codeOrigin .down source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .map v source => exact codeOrigin (.map v) source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .select source selected => exact codeOrigin (.select selected) source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeOrigin (.focusMinimal minimal bound) source.formed (fun _ h => source.applicationOrigin h) member
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.applicationOrigin
    {demand : Profile n}
    (source : SortableObs env U registry Γ locals σ (.app f arg) demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  match n, demand, footprint, source with
  | _, _, _, .legacy source => exact source.applicationOrigin member
  | _, _, _, .code _ source => exact source.applicationOrigin member
  | _, _, _, .app fn argument arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, _, _, _, fn, _, argument, arguments, admitted⟩, ⟨.refl⟩, fun _ h => h⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included⟩
  | _, _, _, .action source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path change⟩, included⟩
  | _, _, _, .rowShift source =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, included⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.applicationOrigin
    {demand : Profile n}
    (source : SortableCert env U registry Γ locals σ (.app f arg) relevant demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : SortableAppOrigin env U registry Γ locals σ f arg,
      Nonempty (GeneralOutputPath env U registry Γ origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  match n, demand, footprint, source with
  | _, _, _, .ofCode source _ => exact source.applicationOrigin member
  | _, _, _, .observe source _ => exact source.applicationOrigin member
  | _, _, _, .seed source _ => exact source.applicationOrigin member
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, .familyPad source => exact codeOrigin .familyPad source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .down source => exact codeOrigin .down source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .map v source => exact codeOrigin (.map v) source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .select source selected => exact codeOrigin (.select selected) source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeOrigin (.focusMinimal minimal bound) source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .sortPad source => exact codeOrigin .sortPad source.formed (fun _ h => source.applicationOrigin h) member
  | _, _, _, .support action source => exact codeOrigin (.support action) source.formed (fun _ h => source.applicationOrigin h) member
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

end
def GeneralOutputPath.height : {n : Nat} → {a : Atom n} →
    GeneralOutputPath env U registry Γ (source : Atom r) a → Nat
  | _, _, .refl => r
  | _, _, .action path _ => path.height
  | n, _, .code path _ _ => max n path.height
  | n + 1, _, .pad path => max (n + 1) path.height
  | _, _, .unpad path => path.height

theorem GeneralOutputPath.bounds
    (path : GeneralOutputPath env U registry Γ (source : Atom r) (a : Atom n)) :
    r ≤ path.height ∧ n ≤ path.height := by
  induction path with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | action path act ih => exact ih
  | code path act formed ih | pad path ih =>
    exact ⟨Nat.le_trans ih.1 (Nat.le_max_right _ _), Nat.le_max_left _ _⟩
  | unpad path ih => exact ⟨ih.1, Nat.le_trans (Nat.le_succ _) ih.2⟩

noncomputable def GeneralOutputPath.normalize
    (path : GeneralOutputPath env U registry Γ (source : Atom r) (a : Atom n))
    (N : Nat) (bound : path.height ≤ N) :
    AtomAction env U registry Γ (raiseAtom N (Nat.le_trans path.bounds.1 bound) source)
      (raiseAtom N (Nat.le_trans path.bounds.2 bound) a) := by
  induction path with
  | refl => exact .view (.refl _)
  | action path act ih => exact .comp (ih bound) (AtomAction.raise (Nat.le_trans path.bounds.2 bound) act)
  | code path act formed ih =>
    have hs := Nat.le_trans (Nat.le_max_right _ _) bound
    have hout := Nat.le_trans (Nat.le_max_left _ _) bound
    have hin := Nat.le_trans path.bounds.2 hs
    have hf := (SortableCodeAction.raiseTo (env := env) (U := U) (registry := registry)
      (target := Γ) (relevant := true) hin).preservesSort formed
    rw [raiseProfile_singleton] at hf
    exact .comp (ih hs) (.code (act.atomAtGrade hin hout) hf)
  | pad path ih =>
    have hs := Nat.le_trans (Nat.le_max_right _ _) bound
    simpa only [raiseAtom_pad] using ih hs
  | unpad path ih => simpa only [raiseAtom_pad] using ih bound

end Lean4Lean.AnchoredSource.Adapted
