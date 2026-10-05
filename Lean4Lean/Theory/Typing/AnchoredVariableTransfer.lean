import Lean4Lean.Theory.Typing.AnchoredVariableTrace

/-! Interpret a normalized variable trace at its original grade. Intermediate
views may have a higher grade; the input and final demand do not change grade.
The concrete support is raised, mapped by the finite view, then projected. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem raiseProfile_trans {n k N : Nat} (hn : n ≤ k) (hk : k ≤ N) (p : Profile n) :
    raiseProfile N hk (raiseProfile k hn p) = raiseProfile N (Nat.le_trans hn hk) p := by
  induction N with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp only [raiseProfile_self]
  | succ N ih =>
    by_cases he : k = N + 1
    · subst k; simp only [raiseProfile_self]
    · have hk' : k ≤ N := by omega
      rw [raiseProfile_step hk', raiseProfile_step (Nat.le_trans hn hk'), ih hk']

theorem Footprint.atGrade_raise {footprint : Footprint} {n N : Nat}
    (h : n ≤ N) (bounded : ∀ i need, (i, need) ∈ footprint → need.rank ≤ n) :
    footprint.atGrade N = raiseProfile N h (footprint.atGrade n) := by
  induction footprint with
  | nil => exact (raiseProfile_empty h).symm
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    have hn := bounded i need List.mem_cons_self
    have hN := Nat.le_trans hn h
    have hrest := ih (fun i need hm => bounded i need (List.mem_cons_of_mem _ hm))
    change (need.atGrade N).union (Footprint.atGrade N rest) =
      raiseProfile N h ((need.atGrade n).union (Footprint.atGrade n rest))
    rw [raiseProfile_union, hrest]
    simp only [Need.atGrade, dif_pos hn, dif_pos hN, raiseProfile_trans]

def lowerProfile : {N : Nat} → (n : Nat) → n ≤ N → Profile N → Profile n
  | 0, n, h, p => (show n = 0 by omega) ▸ p
  | N + 1, n, h, p =>
    if he : n = N + 1 then he.symm ▸ p
    else lowerProfile n (by omega) p.down

@[simp] theorem lowerProfile_self (p : Profile n) :
    lowerProfile n (Nat.le_refl n) p = p := by
  cases n <;> simp [lowerProfile]

theorem lowerProfile_step {n N : Nat} (h : n ≤ N) (p : Profile (N + 1)) :
    lowerProfile n (Nat.le_succ_of_le h) p = lowerProfile n h p.down := by
  simp only [lowerProfile, dif_neg (show n ≠ N + 1 by omega)]

private theorem raise_typed {n N : Nat} (h : n ≤ N) {p d : Profile n}
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

private theorem raise_sort {n N : Nat} (h : n ≤ N) {d : Profile n}
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

private theorem lower_sort {n N : Nat} (h : n ≤ N) {d : Profile N}
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

private theorem lower_typed {n N : Nat} (h : n ≤ N) {p : Profile n} {d : Profile N}
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

private theorem raise_code {n N : Nat} (h : n ≤ N) (henv : env.Ordered)
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

private theorem lower_code {n N : Nat} (h : n ≤ N) (henv : env.Ordered)
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

private theorem raise_related {n N : Nat} (h : n ≤ N) (henv : env.Ordered)
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

private theorem lower_related {n N : Nat} (h : n ≤ N) (henv : env.Ordered)
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

noncomputable def VariableTrace.mapSupport
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) (support : Profile n) : Profile n :=
  lowerProfile n (Nat.le_trans trace.output_bound hN)
    ((trace.normalize N hN).mapType (raiseProfile N (Nat.le_trans trace.output_bound hN) support))

theorem VariableTrace.mapSupport_sort
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) {support : Profile n}
    (ht : support.HasType (.sort relevant)) :
    (trace.mapSupport N hN support).HasType (.sort relevant) :=
  lower_sort _ ((trace.normalize N hN).mapType_sort (raise_sort _ ht))

theorem VariableTrace.mapSupport_typed
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N)
    (bounded : ∀ j need, (j, need) ∈ footprint → need.rank ≤ n)
    {support : Profile n} (ht : (footprint.atGrade n).HasType support) :
    demand.HasType (trace.mapSupport N hN support) := by
  apply lower_typed
  apply (trace.normalize N hN).mapType_typed
  rw [Footprint.atGrade_raise (Nat.le_trans trace.output_bound hN) bounded]
  exact raise_typed _ ht

theorem VariableTrace.codeMap
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) (henv : env.Ordered) (hscoped : registry.Scoped)
    {support : Profile n} (hc : TypeRelated env U registry Γ left right support) :
    TypeRelated env U registry Γ left right (trace.mapSupport N hN support) := by
  apply lower_code _ henv
  apply (trace.normalize N hN).codeMapWith
    (fun view _ _ _ h => view.codeMap henv hscoped h)
  exact raise_code _ henv hc

/-- High internal grades are interpreted and then projected. This preserves
the actual caller domain, original input demand and final output grade. -/
theorem VariableTrace.termMap
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (bounded : ∀ j need, (j, need) ∈ footprint → need.rank ≤ n)
    {support : Profile n} (ht : (footprint.atGrade n).HasType support)
    (hr : Related env U registry Γ left right type (footprint.atGrade n) support) :
    Related env U registry Γ left right type demand (trace.mapSupport N hN support) := by
  apply lower_related _ henv hΓ
  apply (trace.normalize N hN).termMapWith henv hscoped hΓ
    (fun view _ _ _ h => view.codeMap henv hscoped h)
    (fun view _ _ _ _ h => view.termMap henv hscoped hΓ h)
  · rw [Footprint.atGrade_raise (Nat.le_trans trace.output_bound hN) bounded]
    exact raise_typed _ ht
  · rw [Footprint.atGrade_raise (Nat.le_trans trace.output_bound hN) bounded]
    exact raise_related _ henv hr

/-- Lower an actual raised value demand against arbitrary high support. -/
theorem lowerProfile.hasType {n N : Nat} (h : n ≤ N) {p : Profile n} {d : Profile N}
    (ht : (raiseProfile N h p).HasType d) : p.HasType (lowerProfile n h d) :=
  lower_typed h ht

theorem lowerProfile.related {n N : Nat} (h : n ≤ N) (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) {p : Profile n} {d : Profile N}
    (hr : Related env U registry Γ left right type (raiseProfile N h p) d) :
    Related env U registry Γ left right type p (lowerProfile n h d) :=
  lower_related h henv hΓ hr

end Lean4Lean.AnchoredSource
