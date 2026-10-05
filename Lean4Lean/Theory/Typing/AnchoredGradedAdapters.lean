import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Raising finite normal adapters preserves their actual padded endpoints.
The target semantic operations lower only explicitly raised value demands. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource
set_option backward.isDefEq.respectTransparency false

noncomputable def NormalAtomAdapter.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : NormalAtomAdapter env U registry Γ a b) :
    NormalAtomAdapter env U registry Γ (n := n + 1) (.pad a) (.pad b) :=
  AtomAdapter.shift henv hscoped hΓ adapter

noncomputable def NormalProfileAdapter.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (adapter : NormalProfileAdapter env U registry Γ p q) :
    NormalProfileAdapter env U registry Γ p.pad q.pad := by
  change ProfileAdapter env U registry Γ (AdapterNormal.profile p.pad) (AdapterNormal.profile q.pad)
  rw [AdapterNormal.profile_pad, AdapterNormal.profile_pad]
  exact ProfileAdapter.shift henv hscoped hΓ adapter

noncomputable def NormalAtomAdapter.raise
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {n N : Nat} (bound : n ≤ N) {a b : Atom n}
    (adapter : NormalAtomAdapter env U registry Γ a b) :
    NormalAtomAdapter env U registry Γ (raiseAtom N bound a) (raiseAtom N bound b) := by
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
      exact NormalAtomAdapter.pad henv hscoped hΓ (ih hn)

noncomputable def NormalProfileAdapter.raise
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {n N : Nat} (bound : n ≤ N) {p q : Profile n}
    (adapter : NormalProfileAdapter env U registry Γ p q) :
    NormalProfileAdapter env U registry Γ (raiseProfile N bound p) (raiseProfile N bound q) := by
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
      exact NormalProfileAdapter.pad henv hscoped hΓ (ih hn)

theorem Profile.HasType.raise {n N : Nat} (h : n ≤ N) {p d : Profile n}
    (ht : p.HasType d) : (raiseProfile N h p).HasType (raiseProfile N h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact ht
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using ht
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using (ih hn).pad

theorem Profile.HasType.raise_sort {n N : Nat} (h : n ≤ N) {d : Profile n}
    (ht : d.HasType (.sort relevant)) : (raiseProfile N h d).HasType (.sort relevant) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact ht
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using ht
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using (ih hn).pad_sort

theorem Profile.HasType.lower_sort {n N : Nat} (h : n ≤ N) {d : Profile N}
    (ht : d.HasType (.sort relevant)) : (lowerProfile n h d).HasType (.sort relevant) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact ht
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self] using ht
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      exact ih hn (by simpa only [Profile.down_sort] using ht.down)

theorem Profile.HasType.lower {n N : Nat} (h : n ≤ N) {p : Profile n} {d : Profile N}
    (ht : (raiseProfile N h p).HasType d) : p.HasType (lowerProfile n h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact ht
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self, raiseProfile_self] using ht
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      rw [raiseProfile_step hn] at ht
      exact ih hn ht.pad_inv

theorem TypeRelated.raise {n N : Nat} (henv : env.Ordered) (h : n ≤ N)
    {d : Profile n} (hc : TypeRelated env U registry Γ left right d) :
    TypeRelated env U registry Γ left right (raiseProfile N h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact hc
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using hc
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using TypeRelated.pad henv (ih hn)

theorem TypeRelated.lower {n N : Nat} (henv : env.Ordered) (h : n ≤ N)
    {d : Profile N} (hc : TypeRelated env U registry Γ left right d) :
    TypeRelated env U registry Γ left right (lowerProfile n h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact hc
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self] using hc
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      exact ih hn (TypeRelated.down henv hc)

theorem Related.raise {n N : Nat} (henv : env.Ordered) (h : n ≤ N)
    {p d : Profile n} (hr : Related env U registry Γ left right type p d) :
    Related env U registry Γ left right type (raiseProfile N h p) (raiseProfile N h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact hr
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using hr
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using Related.pad henv (ih hn)

theorem Related.lower {n N : Nat} (henv : env.Ordered) (h : n ≤ N)
    (hΓ : OnCtx Γ (env.IsType U)) {p : Profile n} {d : Profile N}
    (hr : Related env U registry Γ left right type (raiseProfile N h p) d) :
    Related env U registry Γ left right type p (lowerProfile n h d) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact hr
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self, raiseProfile_self] using hr
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      rw [raiseProfile_step hn] at hr
      exact ih hn (Related.unpad henv hΓ hr)


private def appendTarget
    (first : ProfileAdapter env U registry Γ source left)
    (second : ProfileAdapter env U registry Γ source right) :
    ProfileAdapter env U registry Γ source (left.union right) := by
  match first with
  | .nil _ => exact second
  | .cons member head tail => exact .cons member head (appendTarget tail second)
termination_by sizeOf first
decreasing_by simp_wf; omega

noncomputable def NormalProfileAdapter.union
    (first : NormalProfileAdapter env U registry Γ p p')
    (second : NormalProfileAdapter env U registry Γ q q') :
    NormalProfileAdapter env U registry Γ (p.union q) (p'.union q') := by
  have joined := appendTarget
    (ProfileAdapter.comp (ProfileAdapter.select (fun _ h => List.mem_append_left _ h)) first)
    (ProfileAdapter.comp (ProfileAdapter.select (fun _ h => List.mem_append_right _ h)) second)
  simpa only [NormalProfileAdapter, AdapterNormal.profile, Profile.union, Profile.atoms,
    Profile.mk, List.map_append] using joined

end Lean4Lean.AnchoredSemantics
