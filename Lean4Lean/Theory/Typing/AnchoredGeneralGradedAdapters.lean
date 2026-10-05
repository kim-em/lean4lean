import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredSourceAdapterCode
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Normalized general adapters move grades by finite explicit shifts. Code
leaves remain code leaves and carry their checked source sort classification. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource
set_option backward.isDefEq.respectTransparency false

mutual
noncomputable def GeneralAtomAdapter.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b) :
    GeneralAtomAdapter env U registry Γ (AdapterNormal.shiftAtom a) (AdapterNormal.shiftAtom b) := by
  match n, a, b, adapter with
  | _, _, _, .refl value => exact .refl _
  | _, _, _, .code action formed =>
    rw [AdapterNormal.shiftAtom_sortable formed,
      AdapterNormal.shiftAtom_sortable (action.preservesSort formed)]
    exact .pad (.code action formed)
  | _ + 1, _, _, .fn keys output =>
    exact .fn (keys.shift henv hscoped hΓ) (output.shift henv hscoped hΓ)
  | _ + 1, _, _, .pad adapter => exact .pad (.pad adapter)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralProfileAdapter.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (adapter : GeneralProfileAdapter env U registry Γ p q) :
    GeneralProfileAdapter env U registry Γ (AdapterNormal.shiftProfile p) (AdapterNormal.shiftProfile q) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.shift henv hscoped hΓ) (tail.shift henv hscoped hΓ)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralKeyProgram.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {old new : Key n} (program : GeneralKeyProgram env U registry Γ old new) :
    GeneralKeyProgram env U registry Γ (AdapterNormal.shiftKey old) (AdapterNormal.shiftKey new) := by
  match program with
  | .refl _ => exact .refl _
  | .input seed arguments => exact .input (seed.shift henv hscoped hΓ) (arguments.shift henv hscoped hΓ)
  | .reanchor admitted => exact .reanchor (AdapterNormal.shiftAdmission henv hscoped hΓ admitted)
  | .domainRekey path typed formed bridge =>
    let view := AdapterNormal.shiftProfileView (U := U) (registry := registry) (Γ := Γ) henv old.input
    exact .domainRekey path (view.mapType_typed typed.pad)
      (view.mapType_sort formed.pad_sort) (view.codeMap henv hscoped (bridge.pad henv))
  | .comp first second => exact .comp (first.shift henv hscoped hΓ) (second.shift henv hscoped hΓ)
termination_by (3 * n + 2, sizeOf program)
decreasing_by all_goals simp_wf; omega
end
noncomputable def GeneralNormalAtomAdapter.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : GeneralNormalAtomAdapter env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Γ (n := n + 1) (.pad a) (.pad b) :=
  GeneralAtomAdapter.shift henv hscoped hΓ adapter

noncomputable def GeneralNormalProfileAdapter.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (adapter : GeneralNormalProfileAdapter env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Γ p.pad q.pad := by
  change GeneralProfileAdapter env U registry Γ (AdapterNormal.profile p.pad) (AdapterNormal.profile q.pad)
  rw [AdapterNormal.profile_pad, AdapterNormal.profile_pad]
  exact GeneralProfileAdapter.shift henv hscoped hΓ adapter

noncomputable def GeneralNormalAtomAdapter.raise
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {n N : Nat} (bound : n ≤ N) {a b : Atom n}
    (adapter : GeneralNormalAtomAdapter env U registry Γ a b) :
    GeneralNormalAtomAdapter env U registry Γ (raiseAtom N bound a) (raiseAtom N bound b) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simpa only [raiseAtom_self] using adapter
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseAtom_self] using adapter
    · have hn : n ≤ N := by omega
      rw [raiseAtom_step hn, raiseAtom_step hn]
      exact GeneralNormalAtomAdapter.pad henv hscoped hΓ (ih hn)

noncomputable def GeneralNormalProfileAdapter.raise
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {n N : Nat} (bound : n ≤ N) {p q : Profile n}
    (adapter : GeneralNormalProfileAdapter env U registry Γ p q) :
    GeneralNormalProfileAdapter env U registry Γ (raiseProfile N bound p) (raiseProfile N bound q) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simpa only [raiseProfile_self] using adapter
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using adapter
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, raiseProfile_step hn]
      exact GeneralNormalProfileAdapter.pad henv hscoped hΓ (ih hn)

private def appendTarget
    (first : GeneralProfileAdapter env U registry Γ source left)
    (second : GeneralProfileAdapter env U registry Γ source right) :
    GeneralProfileAdapter env U registry Γ source (left.union right) := by
  match first with
  | .nil _ => exact second
  | .cons member head tail => exact .cons member head (appendTarget tail second)
termination_by sizeOf first
decreasing_by simp_wf; omega

noncomputable def GeneralNormalProfileAdapter.union
    (first : GeneralNormalProfileAdapter env U registry Γ p p')
    (second : GeneralNormalProfileAdapter env U registry Γ q q') :
    GeneralNormalProfileAdapter env U registry Γ (p.union q) (p'.union q') := by
  have joined := appendTarget
    (GeneralProfileAdapter.comp (GeneralProfileAdapter.select (fun _ h => List.mem_append_left _ h)) first)
    (GeneralProfileAdapter.comp (GeneralProfileAdapter.select (fun _ h => List.mem_append_right _ h)) second)
  simpa only [GeneralNormalProfileAdapter, AdapterNormal.profile, Profile.union, Profile.atoms,
    Profile.mk, List.map_append] using joined

end Lean4Lean.AnchoredSemantics
