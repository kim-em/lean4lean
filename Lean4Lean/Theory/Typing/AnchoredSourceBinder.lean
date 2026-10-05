import Lean4Lean.Theory.Typing.AnchoredSourceEnvelope
import Lean4Lean.Theory.Typing.AnchoredSourceRenaming
import Lean4Lean.Theory.Typing.AnchoredVariableTransfer

/-! Extend a fixed finite source valuation at a binder. Each local demand is
an actual bounded leaf of the input, and receives an actual lowered source
annotation certificate. Older variables retain their original certificates.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def Valuation.push (head : List Need) (tail : Valuation) : Valuation
  | 0 => head
  | i + 1 => tail i

def Footprint.localNeeds : Footprint → List Need
  | [] => []
  | (0, need) :: rest => need :: Footprint.localNeeds rest
  | (_ + 1, _) :: rest => Footprint.localNeeds rest

theorem Footprint.mem_localNeeds :
    need ∈ Footprint.localNeeds required ↔ (0, need) ∈ required := by
  induction required with
  | nil => simp [Footprint.localNeeds]
  | cons entry rest ih =>
    rcases entry with ⟨i, original⟩
    cases i <;> simp [Footprint.localNeeds, ih]

theorem BinderPack.localNeeds {input : Profile n}
    (pack : BinderPack n input required outside) :
    ∀ need ∈ required.localNeeds,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms := by
  induction pack with
  | nil => intro need hm; cases hm
  | «local» original bound rest ih =>
    intro need hm
    rcases List.mem_cons.mp hm with he | hm
    · subst need
      exact ⟨bound, fun _ ha => List.mem_append_left _ ha⟩
    · obtain ⟨hn, hc⟩ := ih need hm
      exact ⟨hn, fun _ ha => List.mem_append_right _ (hc _ ha)⟩
  | external _ _ rest ih => exact ih

private theorem BinderPack.external_mem
    (pack : BinderPack n input required outside)
    (hm : (i + 1, need) ∈ required) : (i, need) ∈ outside := by
  induction pack with
  | nil => cases hm
  | «local» original bound rest ih =>
    rcases List.mem_cons.mp hm with he | hm
    · cases he
    · exact ih hm
  | external j original rest ih =>
    rcases List.mem_cons.mp hm with he | hm
    · have he' : (i, need) = (j, original) := by simpa using he
      exact List.mem_cons.mpr (Or.inl he')
    · exact List.mem_cons_of_mem _ (ih hm)

theorem BinderPack.available
    {available : Valuation}
    (pack : BinderPack n input required outside)
    (resources : outside.Available available) :
    required.Available (Valuation.push required.localNeeds available) := by
  intro i need hm
  cases i with
  | zero => exact Footprint.mem_localNeeds.mpr hm
  | succ i => exact resources i need (pack.external_mem hm)

/-- A certificate returned by the original body child may use any subset of
the fixed local leaves. Its concrete binder pack is consequently covered by
the original function input, as required by a source Pi row. -/
theorem Footprint.pack_available {input : Profile n}
    {required : Footprint} {localNeeds : List Need} {available : Valuation}
    (resources : required.Available (Valuation.push localNeeds available))
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∃ packed outside, BinderPack n packed required outside ∧
      (∀ atom ∈ packed.atoms, atom ∈ input.atoms) ∧ outside.Available available := by
  induction required with
  | nil =>
    refine ⟨.empty, [], .nil, ?_, ?_⟩
    · intro atom hm; cases hm
    · intro i need hm; cases hm
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    obtain ⟨packed, outside, pack, hcovered, havailable⟩ :=
      ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    cases i with
    | zero =>
      have hm := resources 0 need List.mem_cons_self
      refine ⟨(need.atGrade n).union packed, outside, .local need (bounded need hm) pack,
        ?_, havailable⟩
      intro atom ha
      exact (List.mem_append.mp ha).elim (covered need hm atom) (hcovered atom)
    | succ i =>
      refine ⟨packed, (i, need) :: outside, .external i need pack, hcovered, ?_⟩
      intro j original hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        exact resources (i + 1) need List.mem_cons_self
      · exact havailable j original hm

private theorem available_shift
    (h : Footprint.Available footprint available) :
    Footprint.Available (footprint.sourceLift (.skip .refl)) (Valuation.push head available) := by
  intro i need hm
  obtain ⟨⟨j, original⟩, hj, he⟩ := List.mem_map.mp hm
  cases he
  exact h _ _ hj

noncomputable def CodeCert.lower {N : Nat}
    {profile : Profile N}
    (cert : CodeCert env U registry target locals realization expression profile footprint)
    (n : Nat) (bound : n ≤ N) :
    CodeCert env U registry target locals realization expression (lowerProfile n bound profile) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact cert
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self] using cert
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      exact ih cert.down hn

private theorem typed_subset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

/-- A paired argument at the full packed input supplies precisely the fixed
list of local leaf demands. The grade bounds also cover empty leaf demands;
no new source observation is inferred from target relatedness. -/
theorem Fits.push
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {left right : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (fits : Fits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst left) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Fits env U registry (A :: source) target (Locals.push locals)
      (left.cons x) (right.cons y) (Valuation.push localNeeds available) := by
  constructor
  intro index need hm sourceType lookup
  cases lookup with
  | zero =>
    have hn := bounded need hm
    have hc := covered need hm
    simp only [Need.atGrade, dif_pos hn] at hc
    have ht := lowerProfile.hasType hn (typed_subset hc typed)
    have hr : Related env U registry target x y (A.subst left)
        (raiseProfile N hn need.profile) support :=
      Related.of_singletons (fun atom hatom => arguments.singleton_of_mem (hc atom hatom))
    have hl := lowerProfile.related hn henv hTarget hr
    have certificate := (domain.lower need.rank hn).renameSource (.skip .refl)
      (left.cons x) rfl (Locals.push locals)
    refine ⟨⟨_, _, ?_, available_shift domainAvailable, ht, ?_⟩⟩
    · simpa only [← lift_eq_lift'] using certificate
    · simpa only [Subst.cons, lift_subst_cons] using hl
  | succ lookup =>
    obtain ⟨entry⟩ := fits.entry _ need hm _ lookup
    have certificate := entry.certificate.renameSource (.skip .refl)
      (left.cons x) rfl (Locals.push locals)
    refine ⟨⟨entry.support, _, ?_, available_shift entry.available, entry.typed, ?_⟩⟩
    · simpa only [← lift_eq_lift'] using certificate
    · simpa only [Subst.cons, lift_subst_cons] using entry.related

end Lean4Lean.AnchoredSource
