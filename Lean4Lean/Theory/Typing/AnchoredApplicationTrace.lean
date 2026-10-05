import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! A singleton observation of an application has one actual application
leaf. Empty branches contribute no source resources. The remaining path is a
finite sequence of existing views and grade changes. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def AtomView.raise {n N : Nat} {a b : Atom n} (h : n ≤ N)
    (view : AtomView env U registry Γ a b) :
    AtomView env U registry Γ (raiseAtom N h a) (raiseAtom N h b) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact view
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseAtom_self] using view
    · have hn : n ≤ N := by omega
      simpa only [raiseAtom_step hn] using AtomView.pad (ih hn)

theorem raiseAtom_pad {n N : Nat} (h : n + 1 ≤ N) (a : Atom n) :
    raiseAtom N h (.pad a) = raiseAtom N (by omega) a := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : n = N
    · subst n; rw [raiseAtom_self, raiseAtom_step (Nat.le_refl N), raiseAtom_self]
    · have hn : n + 1 ≤ N := by omega
      rw [raiseAtom_step hn, raiseAtom_step (show n ≤ N by omega), ih hn]

inductive AppOutputPath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) {r : Nat} (source : Atom r) : {n : Nat} → Atom n → Type where
  | refl : AppOutputPath env U registry Γ source source
  | view (path : AppOutputPath env U registry Γ source (a : Atom n))
      (change : AtomView env U registry Γ a b) : AppOutputPath env U registry Γ source b
  | pad (path : AppOutputPath env U registry Γ source (a : Atom n)) :
      AppOutputPath env U registry Γ source (n := n + 1) (.pad a)
  | unpad (path : AppOutputPath env U registry Γ source (n := n + 1) (.pad (a : Atom n))) :
      AppOutputPath env U registry Γ source a
  | rowShift (path : AppOutputPath env U registry Γ source (n := n + 1) (.fn (key : Key n) output)) :
      AppOutputPath env U registry Γ source (n := n + 2) (.fn key.pad (.pad output))

def AppOutputPath.height : {n : Nat} → {out : Atom n} →
    AppOutputPath env U registry Γ (source : Atom r) out → Nat
  | _, _, .refl => r
  | _, _, .view path _ => path.height
  | n + 1, _, .pad path => max (n + 1) path.height
  | _, _, .unpad path => path.height
  | n + 2, _, .rowShift path => max (n + 2) path.height

theorem AppOutputPath.bounds (path : AppOutputPath env U registry Γ (source : Atom r) (out : Atom n)) :
    r ≤ path.height ∧ n ≤ path.height := by
  induction path with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | view path change ih => exact ih
  | pad | rowShift => exact ⟨Nat.le_trans ‹_ ∧ _›.1 (Nat.le_max_right _ _), Nat.le_max_left _ _⟩
  | unpad path ih => exact ⟨ih.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) ih.2⟩

noncomputable def AppOutputPath.normalize
    (path : AppOutputPath env U registry Γ (source : Atom r) (out : Atom n))
    (N : Nat) (bound : path.height ≤ N) :
    AtomView env U registry Γ
      (raiseAtom N (Nat.le_trans path.bounds.1 bound) source)
      (raiseAtom N (Nat.le_trans path.bounds.2 bound) out) := by
  induction path with
  | refl => exact .refl _
  | view path change ih => exact .trans (ih bound) (AtomView.raise (Nat.le_trans path.bounds.2 bound) change)
  | pad path ih =>
    have hp := Nat.le_trans (Nat.le_max_right _ _) bound
    simpa only [raiseAtom_pad] using ih hp
  | unpad path ih => simpa only [raiseAtom_pad] using ih bound
  | @rowShift n key output path ih =>
    have hp := Nat.le_trans (Nat.le_max_right _ _) bound
    have ho : n + 2 ≤ N := Nat.le_trans (Nat.le_max_left _ _) bound
    have shift := AtomView.raise ho (AtomView.commutePadFn (env := env) (U := U)
      (registry := registry) (Γ := Γ) key output)
    rw [raiseAtom_pad] at shift
    exact .trans (ih hp) shift

theorem Obs.app_empty_footprint
    (observation : Obs env U registry Γ locals σ (.app f a) demand footprint)
    (empty : demand = .empty) : footprint = [] := by
  match observation with
  | .empty => rfl
  | .app .. => cases empty
  | .union left right =>
    have parts := List.append_eq_nil_iff.mp empty
    rw [left.app_empty_footprint parts.1, right.app_empty_footprint parts.2]
    rfl
  | .view .. => cases empty
  | .pad source => exact source.app_empty_footprint (List.map_eq_nil_iff.mp empty)
  | .unpad source =>
    exact source.app_empty_footprint (by rw [empty]; rfl)
  | .rowShift .. => cases empty
termination_by sizeOf observation

structure AppOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  rank : Nat
  key : Key rank
  output : Atom rank
  functionFootprint : Footprint
  argumentFootprint : Footprint
  function : Obs env U registry Γ locals σ f (Profile.fn key output) functionFootprint
  argument : Obs env U registry Γ locals σ a key.input argumentFootprint
  admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)

theorem Obs.application_factor {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.app f a) demand footprint)
    (output : Atom n) (single : demand = .singleton output) :
    ∃ origin : AppOrigin env U registry Γ locals σ f a,
      Nonempty (AppOutputPath env U registry Γ origin.output output) ∧
      footprint = origin.functionFootprint ++ origin.argumentFootprint := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .app fn arg admitted =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, _, _, fn, arg, admitted⟩, ⟨.refl⟩, rfl⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.app_empty_footprint hs.1
      obtain ⟨origin, path, footprint⟩ := right.application_factor output hs.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint]⟩
    · obtain ⟨origin, path, footprint⟩ := left.application_factor output hs.1
      have hf := right.app_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint]⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor _ rfl
    exact ⟨origin, ⟨.view path change⟩, footprint⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor first he
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor (.pad output)
      (by rw [single, Profile.pad_singleton])
    exact ⟨origin, ⟨.unpad path⟩, footprint⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor _ rfl
    exact ⟨origin, ⟨.rowShift path⟩, footprint⟩
termination_by sizeOf observation

end Lean4Lean.AnchoredSource
