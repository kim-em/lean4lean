import Lean4Lean.Theory.Typing.AnchoredProfileData

/-! Finite demands with frozen argument keys and atomic function outputs.
Domain support belongs to covering Pi profiles, not to value keys. Function
output conjunction is represented by separate rows, never by one fused atom.
These judgments contain no evaluation, source observation, or logical relation.
Raw typing and semantic domain links belong to the later interpretation. -/

namespace Lean4Lean.AnchoredProfiles

inductive AtomData (P A : Type) where
  | sort (relevant : Bool)
  | fn (key : KeyData P) (output : A)
  | pi (prototypeDomain prototypeCodomain : VExpr) (domain : P)
      (rows : List (KeyData P × P))
  | pad (atom : A)
  | family (data : FamilyData P)
  | ctor (data : ConstructorData P)
  | record (data : RecordData P)

def Atom : Nat → Type
  | 0 => Bool
  | n + 1 => AtomData (List (Atom n)) (Atom n)

def Profile (n : Nat) : Type := List (Atom n)

abbrev Key (n : Nat) := KeyData (Profile n)

def Profile.atoms {n : Nat} (profile : Profile n) : List (Atom n) := profile

def Profile.mk {n : Nat} (atoms : List (Atom n)) : Profile n := atoms

def Profile.empty : Profile n := .mk []
def Profile.singleton (atom : Atom n) : Profile n := .mk [atom]
def Profile.sort {n : Nat} (relevant : Bool) : Profile n :=
  match n with
  | 0 => [relevant]
  | _ + 1 => [.sort relevant]
def Profile.union (left right : Profile n) : Profile n := .mk (left.atoms ++ right.atoms)

def Profile.Nonempty (profile : Profile n) : Prop := profile.atoms ≠ []

private def Covers (R : α → α → Prop) (left right : List α) : Prop :=
  ∀ atom ∈ left, ∃ other ∈ right, R atom other

/-- One rank's judgments. The only instance is constructed by recursion on
rank below; callers do not supply any of these fields. -/
private structure Checks (n : Nat) where
  le : Profile n → Profile n → Prop
  wf : Profile n → Prop
  typed : Profile n → Profile n → Prop

private def KeyWF (lower : Checks n) (key : Key n) : Prop :=
  lower.wf key.input

private def RowsLE (lower : Checks n) (left right : List (Key n × Profile n)) : Prop :=
  ∀ key output, (key, output) ∈ left →
    ∃ output', (key, output') ∈ right ∧ lower.le output output'

private def AtomLE (lower : Checks n) : Atom (n + 1) → Atom (n + 1) → Prop
  | .sort r, .sort s => r = s
  | .fn key output, .fn key' output' =>
    key = key' ∧ lower.le (.singleton output) (.singleton output')
  | .pi A B domain rows, .pi A' B' domain' rows' =>
    A = A' ∧ B = B' ∧ lower.le domain domain' ∧ RowsLE lower rows rows'
  | .pad a, .pad b => lower.le (.singleton a) (.singleton b)
  | .family a, .family b => a = b
  | .ctor a, .ctor b => a = b
  | .record a, .record b => a = b
  | _, _ => False

private def RequestWF (lower : Checks n) (request : DataRequest (Profile n)) : Prop :=
  lower.wf request.input ∧ lower.wf request.support

private def FamilyWF (lower : Checks n) (data : FamilyData (Profile n)) : Prop :=
  ∀ request ∈ data.arguments, RequestWF lower request

private def ConstructorWF (lower : Checks n) (data : ConstructorData (Profile n)) : Prop :=
  FamilyWF lower data.family ∧ ∀ request ∈ data.arguments, RequestWF lower request

private def RecordWF (lower : Checks n) (data : RecordData (Profile n)) : Prop :=
  FamilyWF lower data.family ∧ ∀ entry ∈ data.fields, RequestWF lower entry.2

private def AtomWF (lower : Checks n) : Atom (n + 1) → Prop
  | .sort _ => True
  | .fn key output => KeyWF lower key ∧ lower.wf (.singleton output)
  | .pi _ _ domain rows =>
    lower.typed domain (.sort true) ∧
      ∀ key output, (key, output) ∈ rows →
        lower.typed key.input domain ∧ lower.wf output
  | .pad atom => lower.wf (.singleton atom)
  | .family data => FamilyWF lower data
  | .ctor data => ConstructorWF lower data
  | .record data => RecordWF lower data

private def AtomTyped (lower : Checks n) : Atom (n + 1) → Atom (n + 1) → Prop
  | .sort _, .sort relevant => relevant = true
  | .pi _ _ _ rows, .sort relevant =>
    ∀ key output, (key, output) ∈ rows → lower.typed output (.sort relevant)
  | .fn key output, .pi _ _ _ rows =>
    ∃ type, (key, type) ∈ rows ∧ lower.typed (.singleton output) type
  | .pad atom, .pad type => lower.typed (.singleton atom) (.singleton type)
  | .pad atom, .sort relevant => lower.typed (.singleton atom) (.sort relevant)
  | .family data, .sort relevant => data.relevant = relevant
  | .ctor data, .family type => data.family = type
  | .record data, .family type => data.family = type
  | _, _ => False

private def zeroRelevant : Atom 0 → Bool := id

private def checks : (n : Nat) → Checks n
  | 0 => {
      le := fun left right => Covers (fun a b => zeroRelevant a = zeroRelevant b)
        left.atoms right.atoms
      wf := fun _ => True
      typed := fun value type => ∀ atom ∈ value.atoms,
        ∃ other ∈ type.atoms, zeroRelevant other = true }
  | n + 1 =>
    let lower := checks n
    let wf := fun profile => ∀ atom ∈ profile.atoms, AtomWF lower atom
    { le := fun left right => Covers (AtomLE lower) left.atoms right.atoms
      wf := wf
      typed := fun value type => wf value ∧ wf type ∧
        ∀ atom ∈ value.atoms, ∃ other ∈ type.atoms, AtomTyped lower atom other }

def Profile.LE (left right : Profile n) : Prop := (checks n).le left right
def Profile.WF (profile : Profile n) : Prop := (checks n).wf profile
def Profile.HasType (value type : Profile n) : Prop := (checks n).typed value type

def Key.WF (key : Key n) : Prop := KeyWF (checks n) key

def Rows.LE (left right : List (Key n × Profile n)) : Prop :=
  RowsLE (checks n) left right

def Profile.fn (key : Key n) (output : Atom n) : Profile (n + 1) :=
  .singleton (.fn key output)

def Profile.pi (A B : VExpr) (domain : Profile n)
    (rows : List (Key n × Profile n)) : Profile (n + 1) :=
  .singleton (.pi A B domain rows)

/-- Retain a finite demand at the next ambient rank without exposing another
function or type constructor. -/
def Profile.pad (profile : Profile n) : Profile (n + 1) :=
  profile.map AtomData.pad

def Atom.down : Atom (n + 1) → Profile n
  | .sort relevant => .sort relevant
  | .pad atom => .singleton atom
  | .fn .. | .pi .. | .family .. | .ctor .. | .record .. => .empty

def Profile.down (profile : Profile (n + 1)) : Profile n :=
  profile.flatMap Atom.down

def Key.pad (key : Key n) : Key (n + 1) :=
  { domain := key.domain, anchor := key.anchor, input := key.input.pad }

instance : LE (Profile n) := ⟨Profile.LE⟩

theorem Profile.le_refl (profile : Profile n) : profile ≤ profile := by
  induction n with
  | zero => exact fun atom h => ⟨atom, h, rfl⟩
  | succ n ih =>
    intro atom h
    refine ⟨atom, h, ?_⟩
    cases atom with
    | sort | family | ctor | record => rfl
    | pad atom => exact ih (.singleton atom)
    | fn key output => exact ⟨rfl, ih (.singleton output)⟩
    | pi A B domain rows =>
      exact ⟨rfl, rfl, ih domain, fun key output h => ⟨output, h, ih output⟩⟩

theorem Profile.le_trans {left middle right : Profile n}
    (hl : left ≤ middle) (hr : middle ≤ right) : left ≤ right := by
  induction n with
  | zero =>
    intro atom h
    obtain ⟨mid, hm, h₁⟩ := hl atom h
    obtain ⟨last, ht, h₂⟩ := hr mid hm
    exact ⟨last, ht, h₁.trans h₂⟩
  | succ n ih =>
    intro atom h
    obtain ⟨mid, hm, h₁⟩ := hl atom h
    obtain ⟨last, ht, h₂⟩ := hr mid hm
    refine ⟨last, ht, ?_⟩
    cases atom <;> cases mid <;> cases last <;>
      simp only [AtomLE] at h₁ h₂ ⊢
    all_goals try contradiction
    · exact h₁.trans h₂
    · exact ⟨h₁.1.trans h₂.1, ih h₁.2 h₂.2⟩
    · refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
        ih h₁.2.2.1 h₂.2.2.1, ?_⟩
      intro key output h
      obtain ⟨mid, hm, h₁⟩ := h₁.2.2.2 key output h
      obtain ⟨last, ht, h₂⟩ := h₂.2.2.2 key mid hm
      exact ⟨last, ht, ih h₁ h₂⟩
    · exact ih h₁ h₂
    all_goals exact h₁.trans h₂

theorem Profile.Nonempty.mono {left right : Profile n}
    (h : left.Nonempty) (hle : left ≤ right) : right.Nonempty := by
  intro he
  obtain ⟨atom, ha⟩ := List.exists_mem_of_ne_nil left.atoms h
  cases n with
  | zero =>
    obtain ⟨other, ho, _⟩ := hle atom ha
    rw [he] at ho
    cases ho
  | succ n =>
    obtain ⟨other, ho, _⟩ := hle atom ha
    rw [he] at ho
    cases ho

theorem Profile.le_union_left (left right : Profile n) : left ≤ left.union right := by
  cases n <;> intro atom h
  all_goals
    obtain ⟨other, ho, hle⟩ := left.le_refl atom h
    exact ⟨other, List.mem_append_left _ ho, hle⟩

theorem Profile.le_union_right (left right : Profile n) : right ≤ left.union right := by
  cases n <;> intro atom h
  all_goals
    obtain ⟨other, ho, hle⟩ := right.le_refl atom h
    exact ⟨other, List.mem_append_right _ ho, hle⟩

theorem Profile.union_le {left right upper : Profile n}
    (hl : left ≤ upper) (hr : right ≤ upper) : left.union right ≤ upper := by
  cases n <;> intro atom h
  all_goals
    rcases List.mem_append.mp h with h | h
    · exact hl atom h
    · exact hr atom h

theorem Profile.WF.union {left right : Profile n} (hl : left.WF) (hr : right.WF) :
    (left.union right).WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro atom h
    rcases List.mem_append.mp h with h | h
    · exact hl atom h
    · exact hr atom h

theorem Profile.HasType.wf_value {value type : Profile n} (h : value.HasType type) :
    value.WF := by
  cases n with
  | zero => trivial
  | succ n => exact h.1

theorem Profile.HasType.wf_type {value type : Profile n} (h : value.HasType type) :
    type.WF := by
  cases n with
  | zero => trivial
  | succ n => exact h.2.1

theorem Profile.HasType.singleton_of_mem {value type : Profile n}
    (h : value.HasType type) (hm : atom ∈ value.atoms) :
    (Profile.singleton atom).HasType type := by
  cases n with
  | zero =>
    intro a ha
    have he : a = atom := List.mem_singleton.mp ha
    cases he
    exact h _ hm
  | succ n =>
    refine ⟨?_, h.2.1, ?_⟩
    · intro a ha
      have he : a = atom := List.mem_singleton.mp ha
      cases he
      exact h.1 _ hm
    · intro a ha
      have he : a = atom := List.mem_singleton.mp ha
      cases he
      exact h.2.2 _ hm

/-- Enlarge the available type demands without changing the value demand.
Covariance retains the same frozen argument key. -/
theorem Profile.HasType.enlarge {value type type' : Profile n}
    (h : value.HasType type) (hle : type ≤ type') (hw : type'.WF) :
    value.HasType type' := by
  induction n with
  | zero =>
    intro atom ha
    obtain ⟨old, ho, ht⟩ := h atom ha
    obtain ⟨new, hn, he⟩ := hle old ho
    exact ⟨new, hn, he ▸ ht⟩
  | succ n ih =>
    refine ⟨h.1, hw, ?_⟩
    intro atom ha
    obtain ⟨old, ho, ht⟩ := h.2.2 atom ha
    obtain ⟨new, hn, he⟩ := hle old ho
    have hnwf := hw new hn
    refine ⟨new, hn, ?_⟩
    cases atom <;> cases old <;> cases new <;>
      simp only [AtomLE, AtomTyped, AtomWF] at ht he hnwf ⊢
    all_goals try contradiction
    · exact he ▸ ht
    · obtain ⟨output, hm, hq⟩ := ht
      obtain ⟨output', hm', hle⟩ := he.2.2.2 _ _ hm
      exact ⟨output', hm', ih hq hle (hnwf.2 _ _ hm').2⟩
    · exact he ▸ ht
    · exact he ▸ ht
    · exact ih ht he hnwf
    all_goals exact he ▸ ht

/-- Restrict a value observation only when its smaller syntax remains
intrinsically well formed. In particular a smaller Pi domain must still
type the input of every retained row. -/
theorem Profile.HasType.restrict {value value' type : Profile n}
    (h : value'.HasType type) (hle : value ≤ value') (hw : value.WF) :
    value.HasType type := by
  induction n with
  | zero =>
    intro atom ha
    obtain ⟨old, ho, _⟩ := hle atom ha
    exact h old ho
  | succ n ih =>
    refine ⟨hw, h.2.1, ?_⟩
    intro atom ha
    obtain ⟨old, ho, he⟩ := hle atom ha
    obtain ⟨typeAtom, ht, hat⟩ := h.2.2 old ho
    have hmwf := hw atom ha
    refine ⟨typeAtom, ht, ?_⟩
    cases atom <;> cases old <;> cases typeAtom <;>
      simp only [AtomLE, AtomTyped, AtomWF] at he hat hmwf ⊢
    all_goals try contradiction
    · exact hat
    · obtain ⟨rfl, he⟩ := he
      obtain ⟨output, hm, hq⟩ := hat
      exact ⟨output, hm, ih hq he hmwf.2⟩
    · intro key output hm
      obtain ⟨output', hm', he⟩ := he.2.2.2 key output hm
      exact ih (hat key output' hm') he (hmwf.2 key output hm).2
    · exact ih hat he hmwf
    · exact ih hat he hmwf
    all_goals cases he; exact hat

/-- A finite union of already typed demands needs no new value demand. -/
theorem Profile.HasType.union {left right type : Profile n}
    (hl : left.HasType type) (hr : right.HasType type) :
    (left.union right).HasType type := by
  cases n with
  | zero =>
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl atom ha
    · exact hr atom ha
  | succ n =>
    refine ⟨hl.wf_value.union hr.wf_value, hl.wf_type, ?_⟩
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl.2.2 atom ha
    · exact hr.2.2 atom ha

theorem Profile.HasType.union_types {left right type type' : Profile n}
    (hl : left.HasType type) (hr : right.HasType type') :
    (left.union right).HasType (type.union type') :=
  (hl.enlarge (type.le_union_left type') (hl.wf_type.union hr.wf_type)).union
    (hr.enlarge (type.le_union_right type') (hl.wf_type.union hr.wf_type))

theorem Key.wf_iff (key : Key n) : key.WF ↔ key.input.WF := Iff.rfl

theorem Profile.WF.sort (relevant : Bool) : (Profile.sort (n := n) relevant).WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro atom ha
    have he : atom = .sort relevant := List.mem_singleton.mp ha
    cases he
    trivial

theorem Profile.WF.empty : (Profile.empty (n := n)).WF := by
  cases n with
  | zero => trivial
  | succ n => exact fun atom ha => nomatch ha

theorem Profile.WF.fn_iff {key : Key n} {output : Atom n} :
    (Profile.fn key output).WF ↔ key.WF ∧ (Profile.singleton output).WF := by
  constructor
  · intro h
    exact h _ (List.mem_singleton_self _)
  · intro h atom ha
    have he : atom = .fn key output := List.mem_singleton.mp ha
    cases he
    exact h

theorem Profile.WF.pi_iff {domain : Profile n} {rows : List (Key n × Profile n)} :
    (Profile.pi A B domain rows).WF ↔
      domain.HasType (.sort true) ∧
        ∀ key output, (key, output) ∈ rows →
          key.input.HasType domain ∧ output.WF := by
  constructor
  · intro h
    exact h _ (List.mem_singleton_self _)
  · intro h atom ha
    have he : atom = .pi A B domain rows := List.mem_singleton.mp ha
    cases he
    exact h

theorem Profile.fn_le_fn_iff {key : Key n} {output output' : Atom n} :
    Profile.fn key output ≤ Profile.fn key output' ↔
      Profile.singleton output ≤ Profile.singleton output' := by
  constructor
  · intro h
    obtain ⟨other, hm, ht⟩ := h _ (List.mem_singleton_self _)
    have he : other = .fn key output' := List.mem_singleton.mp hm
    cases he
    exact ht.2
  · intro h atom ha
    have he : atom = .fn key output := List.mem_singleton.mp ha
    cases he
    exact ⟨.fn key output', List.mem_singleton_self _, rfl, h⟩

theorem Profile.pi_le_pi_iff {domain domain' : Profile n}
    {rows rows' : List (Key n × Profile n)} :
    Profile.pi A B domain rows ≤ Profile.pi A B domain' rows' ↔
      domain ≤ domain' ∧ Rows.LE rows rows' := by
  constructor
  · intro h
    obtain ⟨other, hm, ht⟩ := h _ (List.mem_singleton_self _)
    have he : other = .pi A B domain' rows' := List.mem_singleton.mp hm
    cases he
    exact ht.2.2
  · intro h atom ha
    have he : atom = .pi A B domain rows := List.mem_singleton.mp ha
    cases he
    exact ⟨.pi A B domain' rows', List.mem_singleton_self _, rfl, rfl, h⟩

/-- Domination can refine an atomic output, but cannot choose a different
raw domain, anchor, or input observation. -/
theorem Profile.le_fn_inv {left right : Profile (n + 1)}
    (hle : left ≤ right) (hmem : AtomData.fn key output ∈ left.atoms) :
    ∃ output', AtomData.fn key output' ∈ right.atoms ∧
      Profile.singleton output ≤ Profile.singleton output' := by
  obtain ⟨other, hm, hdom⟩ := hle _ hmem
  cases other with
  | sort | family | ctor | record => contradiction
  | pi => contradiction
  | pad => contradiction
  | fn key' output' =>
    obtain ⟨rfl, hdom⟩ := hdom
    exact ⟨output', hm, hdom⟩

/-- A dominating Pi retains both raw prototypes and refines only its finite
domain and the outputs at existing row keys. -/
theorem Profile.pi_le_inv {left right : Profile (n + 1)}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (hle : left ≤ right) (hmem : AtomData.pi A B domain rows ∈ left.atoms) :
    ∃ (domain' : Profile n) (rows' : List (Key n × Profile n)),
      AtomData.pi A B domain' rows' ∈ right.atoms ∧
      domain ≤ domain' ∧ Rows.LE rows rows' := by
  obtain ⟨other, hm, hdom⟩ := hle _ hmem
  cases other with
  | sort | fn | pad | family | ctor | record => contradiction
  | pi A' B' domain' rows' =>
    obtain ⟨rfl, rfl, hd, hr⟩ := hdom
    exact ⟨domain', rows', hm, hd, hr⟩

theorem Profile.sort_le_mem {bound : Profile (n + 1)}
    (hle : Profile.sort relevant ≤ bound) : AtomData.sort relevant ∈ bound.atoms := by
  obtain ⟨other, hm, hdom⟩ := hle _ (List.mem_singleton_self _)
  cases other with
  | fn | pi | pad | family | ctor | record => contradiction
  | sort s => cases hdom; exact hm

theorem Profile.sort_le_mem_zero {bound : Profile 0}
    (hle : Profile.sort relevant ≤ bound) : relevant ∈ bound.atoms := by
  obtain ⟨other, hm, hdom⟩ := hle _ (List.mem_singleton_self _)
  change relevant = other at hdom
  exact hdom ▸ hm

theorem Profile.HasType.empty {type : Profile n} (hw : type.WF) :
    Profile.empty.HasType type := by
  cases n with
  | zero => exact fun atom ha => nomatch ha
  | succ n => exact ⟨Profile.WF.empty (n := n + 1), hw, fun atom ha => nomatch ha⟩

theorem Profile.HasType.sort (relevant : Bool) :
    (Profile.sort (n := n) relevant).HasType (.sort true) := by
  cases n with
  | zero => exact fun _ _ => ⟨true, List.mem_singleton_self _, rfl⟩
  | succ n =>
    refine ⟨Profile.WF.sort (n := n + 1) relevant, Profile.WF.sort (n := n + 1) true, ?_⟩
    intro atom ha
    have he : atom = .sort relevant := List.mem_singleton.mp ha
    cases he
    exact ⟨.sort true, List.mem_singleton_self _, rfl⟩

theorem Profile.HasType.pi_iff {domain : Profile n} {rows : List (Key n × Profile n)} :
    (Profile.pi A B domain rows).HasType (.sort relevant) ↔
      (Profile.pi A B domain rows).WF ∧
        ∀ key output, (key, output) ∈ rows → output.HasType (.sort relevant) := by
  constructor
  · intro h
    obtain ⟨other, hm, ht⟩ := h.2.2 _ (List.mem_singleton_self _)
    have he : other = .sort relevant := List.mem_singleton.mp hm
    cases he
    exact ⟨h.1, ht⟩
  · intro h
    refine ⟨h.1, Profile.WF.sort (n := n + 1) relevant, ?_⟩
    intro atom ha
    have he : atom = .pi A B domain rows := List.mem_singleton.mp ha
    cases he
    exact ⟨.sort relevant, List.mem_singleton_self _, h.2⟩

/-- An empty codomain table fixes neither proof nor data relevance. -/
theorem Profile.HasType.pi_empty {domain : Profile n}
    (hd : domain.HasType (.sort true)) (relevant : Bool) :
    (Profile.pi A B domain []).HasType (.sort relevant) := by
  apply pi_iff.mpr
  exact ⟨Profile.WF.pi_iff.mpr ⟨hd, fun _ _ h => nomatch h⟩,
    fun _ _ h => nomatch h⟩

theorem Profile.HasType.fn {key : Key n} {output : Atom n} {domain : Profile n}
    {rows : List (Key n × Profile n)}
    (hp : (Profile.pi A B domain rows).WF)
    (hrow : (key, type) ∈ rows) (hout : (Profile.singleton output).HasType type) :
    (Profile.fn key output).HasType (.pi A B domain rows) := by
  have hk : key.WF := ((Profile.WF.pi_iff.mp hp).2 _ _ hrow).1.wf_value
  refine ⟨Profile.WF.fn_iff.mpr ⟨hk, hout.wf_value⟩, hp, ?_⟩
  intro atom ha
  have he : atom = .fn key output := List.mem_singleton.mp ha
  cases he
  exact ⟨.pi A B domain rows, List.mem_singleton_self _, type, hrow, hout⟩

/-- The type atom covering a function demand retains its exact key and
types that key's input at its own ambient domain profile. -/
theorem Profile.HasType.fn_inv {key : Key n} {output : Atom n}
    {value type : Profile (n + 1)}
    (h : value.HasType type) (hmem : AtomData.fn key output ∈ value.atoms) :
    ∃ A B domain rows resultType,
      AtomData.pi A B domain rows ∈ type.atoms ∧
      (Profile.pi A B domain rows).WF ∧
      key.WF ∧ key.input.HasType domain ∧
      (key, resultType) ∈ rows ∧ (Profile.singleton output).HasType resultType := by
  obtain ⟨other, hm, ht⟩ := h.2.2 _ hmem
  have hk := h.1 _ hmem
  have hw := h.2.1 _ hm
  cases other with
  | sort | family | ctor | record => contradiction
  | fn => contradiction
  | pad => contradiction
  | pi A B domain rows =>
    obtain ⟨resultType, hr, ht⟩ := ht
    exact ⟨A, B, domain, rows, resultType, hm,
      Profile.WF.pi_iff.mpr hw, hk.1, (hw.2 _ _ hr).1, hr, ht⟩

def Profile.unions (profiles : List (Profile n)) : Profile n :=
  profiles.foldr Profile.union Profile.empty

theorem Profile.unions_le {profiles : List (Profile n)}
    (h : ∀ profile ∈ profiles, profile ≤ upper) : Profile.unions profiles ≤ upper := by
  induction profiles with
  | nil => cases n <;> exact fun atom ha => nomatch ha
  | cons profile profiles ih =>
    exact Profile.union_le (h profile (.head _))
      (ih fun p hp => h p (.tail _ hp))

theorem Profile.HasType.unions {profiles : List (Profile n)} (hw : type.WF)
    (h : ∀ profile ∈ profiles, profile.HasType type) :
    (Profile.unions profiles).HasType type := by
  induction profiles with
  | nil => exact .empty hw
  | cons profile profiles ih =>
    exact (h profile (.head _)).union (ih fun p hp => h p (.tail _ hp))

/-- Proof irrelevance can transfer the empty observation without inspecting
the proof term. A function demand cannot hide a nonempty output behind an
empty or proposition-valued Pi table. This is the intrinsic obligation used
by the proposed strong-derivation proof's `proofIrrel` case. -/
theorem Profile.HasType.proof_empty {value type : Profile n}
    (hv : value.HasType type) (ht : type.HasType (.sort false)) :
    value.atoms = [] := by
  induction n with
  | zero =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom ha
    obtain ⟨other, ho, _⟩ := hv atom ha
    obtain ⟨last, hl, hfalse⟩ := ht other ho
    have he : last = false := List.mem_singleton.mp hl
    cases he
    contradiction
  | succ n ih =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom ha
    obtain ⟨typeAtom, htypeAtom, htyped⟩ := hv.2.2 atom ha
    obtain ⟨last, hl, hsort⟩ := ht.2.2 typeAtom htypeAtom
    have he : last = .sort false := List.mem_singleton.mp hl
    cases he
    cases typeAtom with
    | sort => cases hsort
    | fn | ctor | record => contradiction
    | family data =>
      cases atom <;> simp only [AtomTyped] at htyped
      all_goals try contradiction
      all_goals
        rename_i data
        cases htyped
        exact Bool.noConfusion (data.relevant.symm.trans hsort)
    | pi A B domain rows =>
      cases atom with
      | sort | family | ctor | record => contradiction
      | pi => contradiction
      | pad => contradiction
      | fn key output =>
        obtain ⟨resultType, hr, houtput⟩ := htyped
        have hempty := ih houtput (hsort key resultType hr)
        exact List.cons_ne_nil output [] hempty
    | pad typeAtom =>
      cases atom with
      | sort | family | ctor | record => contradiction
      | fn => contradiction
      | pi => contradiction
      | pad atom => exact List.cons_ne_nil atom [] (ih htyped hsort)

/-! Explicit changes of ambient rank. These preserve the stored demand;
they do not distribute padding through function or Pi constructors. -/

section Padding
set_option backward.isDefEq.respectTransparency false

@[simp] theorem Profile.pad_empty : (Profile.empty (n := n)).pad = .empty := rfl

@[simp] theorem Profile.pad_singleton (atom : Atom n) :
    (Profile.singleton atom).pad = .singleton (.pad atom) := rfl

@[simp] theorem Profile.pad_union (left right : Profile n) :
    (left.union right).pad = left.pad.union right.pad := List.map_append

@[simp] theorem Profile.down_empty : (Profile.empty (n := n + 1)).down = .empty := rfl

@[simp] theorem Profile.down_singleton (atom : Atom (n + 1)) :
    (Profile.singleton atom).down = atom.down := List.append_nil _

@[simp] theorem Profile.down_sort (relevant : Bool) :
    (Profile.sort (n := n + 1) relevant).down = .sort relevant := List.append_nil _

@[simp] theorem Profile.down_union (left right : Profile (n + 1)) :
    (left.union right).down = left.down.union right.down := List.flatMap_append

@[simp] theorem Profile.down_pad (profile : Profile n) : profile.pad.down = profile := by
  induction profile with
  | nil => rfl
  | cons atom profile ih =>
    change atom :: Profile.down (Profile.pad (n := n) profile) = atom :: profile
    rw [ih]

theorem Profile.mem_down_iff {profile : Profile (n + 1)} {atom : Atom n} :
    atom ∈ profile.down.atoms ↔ ∃ high ∈ profile.atoms, atom ∈ high.down.atoms :=
  List.mem_flatMap

private theorem singleton_wf_of_mem {profile : Profile n} (hw : profile.WF)
    (ha : atom ∈ profile.atoms) : (Profile.singleton atom).WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro a hm
    cases List.mem_singleton.mp hm
    exact hw _ ha

theorem Profile.WF.pad {profile : Profile n} (hw : profile.WF) : profile.pad.WF := by
  intro a ha
  change a ∈ List.map AtomData.pad profile at ha
  obtain ⟨b, hb, rfl⟩ := (List.mem_map (f := (AtomData.pad : Atom n → Atom (n + 1)))).mp ha
  exact singleton_wf_of_mem hw hb

theorem Profile.LE.pad {left right : Profile n} (h : left ≤ right) :
    left.pad ≤ right.pad := by
  intro a ha
  change a ∈ List.map AtomData.pad left at ha
  obtain ⟨a, hsource, rfl⟩ := (List.mem_map (f := (AtomData.pad : Atom n → Atom (n + 1)))).mp ha
  cases n with
  | zero =>
    obtain ⟨b, hb, he⟩ := h a hsource
    refine ⟨.pad b, List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro a' hm
    cases List.mem_singleton.mp hm
    exact ⟨b, List.mem_singleton_self _, he⟩
  | succ n =>
    obtain ⟨b, hb, he⟩ := h a hsource
    refine ⟨.pad b, List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro a' hm
    cases List.mem_singleton.mp hm
    exact ⟨b, List.mem_singleton_self _, he⟩

private theorem type_cover {value type : Profile n} (h : value.HasType type)
    (ha : atom ∈ value.atoms) :
    ∃ other ∈ type.atoms, (Profile.singleton atom).HasType (.singleton other) := by
  cases n with
  | zero =>
    obtain ⟨b, hb, ht⟩ := h _ ha
    exact ⟨b, hb, fun _ _ => ⟨b, List.mem_singleton_self _, ht⟩⟩
  | succ n =>
    obtain ⟨b, hb, ht⟩ := h.2.2 _ ha
    refine ⟨b, hb, singleton_wf_of_mem (n := n + 1) h.wf_value ha,
      singleton_wf_of_mem (n := n + 1) h.wf_type hb, ?_⟩
    intro a hm
    cases List.mem_singleton.mp hm
    exact ⟨b, List.mem_singleton_self _, ht⟩

theorem Profile.HasType.pad {value type : Profile n} (h : value.HasType type) :
    value.pad.HasType type.pad := by
  refine ⟨h.wf_value.pad, h.wf_type.pad, ?_⟩
  intro a ha
  change a ∈ List.map AtomData.pad value at ha
  obtain ⟨a, hsource, rfl⟩ := (List.mem_map (f := (AtomData.pad : Atom n → Atom (n + 1)))).mp ha
  obtain ⟨b, hb, ht⟩ := type_cover h hsource
  exact ⟨.pad b, List.mem_map.mpr ⟨b, hb, rfl⟩, ht⟩

theorem Profile.HasType.pad_sort {value : Profile n}
    (h : value.HasType (.sort relevant)) : value.pad.HasType (.sort relevant) := by
  refine ⟨h.wf_value.pad, Profile.WF.sort (n := n + 1) _, ?_⟩
  intro a ha
  change a ∈ List.map AtomData.pad value at ha
  obtain ⟨a, hsource, rfl⟩ := (List.mem_map (f := (AtomData.pad : Atom n → Atom (n + 1)))).mp ha
  exact ⟨.sort relevant, List.mem_singleton_self _, h.singleton_of_mem hsource⟩

private theorem atom_down_wf {profile : Profile (n + 1)} (hw : profile.WF)
    (ha : atom ∈ profile.atoms) : atom.down.WF := by
  cases atom with
  | sort => exact Profile.WF.sort _
  | fn | family | ctor | record => exact Profile.WF.empty
  | pi => exact Profile.WF.empty
  | pad => exact hw _ ha

theorem Profile.WF.down {profile : Profile (n + 1)} (hw : profile.WF) : profile.down.WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro a ha
    obtain ⟨b, hb, ha⟩ := Profile.mem_down_iff.mp ha
    exact atom_down_wf hw hb a ha

private theorem atom_down_le {profile : Profile (n + 1)} (ha : atom ∈ profile.atoms) :
    atom.down ≤ profile.down := by
  cases n <;> intro a hmem
  all_goals
    obtain ⟨b, hb, he⟩ := atom.down.le_refl a hmem
    exact ⟨b, Profile.mem_down_iff.mpr ⟨atom, ha, hb⟩, he⟩

/-- Removing one explicit padding layer preserves finite domination. Pi and
function atoms contribute no demand to this lower-rank projection. -/
theorem Profile.LE.down {left right : Profile (n + 1)} (hle : left ≤ right) :
    left.down ≤ right.down := by
  cases n <;> intro atom hmem
  all_goals
    obtain ⟨upper, hupper, hmember⟩ := Profile.mem_down_iff.mp hmem
    obtain ⟨other, hother, hdom⟩ := hle upper hupper
    cases upper with
    | fn | pi | family | ctor | record => cases hmember
    | sort relevant =>
      cases other with
      | fn | pi | pad | family | ctor | record => contradiction
      | sort s =>
        cases hdom
        exact atom_down_le hother atom hmember
    | pad lower =>
      cases other with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad upper =>
        exact Profile.le_trans hdom (atom_down_le hother) atom hmember

private theorem down_collect {type : Profile n} (ht : type.WF)
    (profile : Profile (n + 1))
    (h : ∀ a ∈ profile.atoms, a.down.HasType type) : profile.down.HasType type := by
  induction profile with
  | nil => exact Profile.HasType.empty ht
  | cons a profile ih =>
    exact (h a (.head _)).union (ih fun b hb => h b (.tail _ hb))

theorem Profile.HasType.down {value type : Profile (n + 1)} (h : value.HasType type) :
    value.down.HasType type.down := by
  apply down_collect h.wf_type.down
  intro a ha
  obtain ⟨b, hb, ht⟩ := h.2.2 a ha
  have embed := atom_down_le hb
  cases a with
  | fn | family | ctor | record => exact .empty h.wf_type.down
  | pi => exact .empty h.wf_type.down
  | sort relevant =>
    cases b with
    | sort r =>
      cases ht
      exact (Profile.HasType.sort relevant).enlarge embed h.wf_type.down
    | fn | family | ctor | record => contradiction
    | pi => contradiction
    | pad => contradiction
  | pad atom =>
    cases b with
    | sort => exact Profile.HasType.enlarge ht embed h.wf_type.down
    | pad => exact Profile.HasType.enlarge ht embed h.wf_type.down
    | fn | family | ctor | record => contradiction
    | pi => contradiction

theorem Profile.HasType.pad_inv {value : Profile n} {type : Profile (n + 1)}
    (h : value.pad.HasType type) : value.HasType type.down := by
  simpa only [Profile.down_pad] using h.down

end Padding

/-! Raw context renaming. All row anchors and finite profiles live in the
ambient context; only a Pi's raw codomain prototype is under its binder. -/

section Renaming
set_option backward.isDefEq.respectTransparency false

def Atom.rename : {n : Nat} → Lift → Atom n → Atom n
  | 0, _, atom => atom
  | n + 1, ρ, atom =>
    let profile := List.map (Atom.rename (n := n) ρ)
    let key := fun k : Key n =>
      { domain := k.domain.lift' ρ, anchor := k.anchor.lift' ρ, input := profile k.input }
    match atom with
    | .sort relevant => .sort relevant
    | .pad atom => .pad (Atom.rename ρ atom)
    | .fn k output => .fn (key k) (Atom.rename ρ output)
    | .pi A B domain rows => .pi (A.lift' ρ) (B.lift' ρ.cons) (profile domain)
        (rows.map fun (k, output) => (key k, profile output))
    | .family data => .family (data.map (·.lift' ρ) profile)
    | .ctor data => .ctor (data.map (·.lift' ρ) profile)
    | .record data => .record (data.map (·.lift' ρ) profile)

def Profile.rename (ρ : Lift) (profile : Profile n) : Profile n :=
  profile.map (Atom.rename ρ)

def Key.rename (ρ : Lift) (key : Key n) : Key n :=
  { domain := key.domain.lift' ρ, anchor := key.anchor.lift' ρ,
    input := key.input.rename ρ }

def Rows.rename (ρ : Lift) (rows : List (Key n × Profile n)) :
    List (Key n × Profile n) :=
  rows.map fun (key, output) => (key.rename ρ, output.rename ρ)

@[simp] theorem Atom.rename_sort :
    Atom.rename (n := n + 1) ρ (.sort relevant) = .sort relevant := rfl

@[simp] theorem Atom.rename_pad (atom : Atom n) :
    Atom.rename (n := n + 1) ρ (.pad atom) = .pad (atom.rename ρ) := rfl

@[simp] theorem Atom.rename_fn {key : Key n} {output : Atom n} :
    Atom.rename (n := n + 1) ρ (.fn key output) =
      .fn (key.rename ρ) (Atom.rename ρ output) := rfl

@[simp] theorem Atom.rename_pi {domain : Profile n} {rows : List (Key n × Profile n)} :
    Atom.rename (n := n + 1) ρ (.pi A B domain rows) =
      .pi (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows) := rfl

@[simp] theorem Atom.rename_family (data : FamilyData (Profile n)) :
    Atom.rename (n := n + 1) ρ (.family data : Atom (n + 1)) =
      .family (data.map (·.lift' ρ) (Profile.rename ρ)) := rfl

@[simp] theorem Atom.rename_ctor (data : ConstructorData (Profile n)) :
    Atom.rename (n := n + 1) ρ (.ctor data : Atom (n + 1)) =
      .ctor (data.map (·.lift' ρ) (Profile.rename ρ)) := rfl

@[simp] theorem Atom.rename_record (data : RecordData (Profile n)) :
    Atom.rename (n := n + 1) ρ (.record data : Atom (n + 1)) =
      .record (data.map (·.lift' ρ) (Profile.rename ρ)) := rfl

@[simp] theorem Profile.rename_empty :
    (Profile.empty (n := n)).rename ρ = .empty := rfl

@[simp] theorem Profile.rename_singleton (atom : Atom n) :
    (Profile.singleton atom).rename ρ = .singleton (atom.rename ρ) := rfl

@[simp] theorem Profile.rename_sort (relevant : Bool) :
    (Profile.sort (n := n) relevant).rename ρ = .sort relevant := by
  cases n <;> rfl

@[simp] theorem Profile.rename_union (left right : Profile n) :
    (left.union right).rename ρ = (left.rename ρ).union (right.rename ρ) :=
  List.map_append

theorem Profile.pad_rename (profile : Profile n) (ρ : Lift) :
    (profile.rename ρ).pad = profile.pad.rename ρ := by
  simp only [pad, rename, List.map_map]
  rfl

@[simp] theorem Profile.rename_pad (profile : Profile n) (ρ : Lift) :
    profile.pad.rename ρ = (profile.rename ρ).pad := (profile.pad_rename ρ).symm

@[simp] theorem Atom.down_rename (atom : Atom (n + 1)) (ρ : Lift) :
    (atom.rename ρ).down = atom.down.rename ρ := by
  cases atom <;> simp only [Atom.rename_sort, Atom.rename_fn, Atom.rename_pi,
    Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record, Atom.down, Profile.rename_sort, Profile.rename_empty,
    Profile.rename_singleton]

@[simp] theorem Profile.down_rename (profile : Profile (n + 1)) (ρ : Lift) :
    (profile.rename ρ).down = profile.down.rename ρ := by
  induction profile with
  | nil => rfl
  | cons atom profile ih =>
    change (atom.rename ρ).down.union (Profile.rename ρ profile).down =
      (atom.down.union (Profile.down profile)).rename ρ
    rw [Atom.down_rename, ih, Profile.rename_union]

theorem Key.pad_rename (key : Key n) (ρ : Lift) :
    (key.rename ρ).pad = key.pad.rename ρ := by
  cases key
  simp only [Key.pad, Key.rename, Profile.pad_rename]

@[simp] theorem Atom.rename_refl (atom : Atom n) : atom.rename .refl = atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp (p : Profile n) : p.rename .refl = p := by
      change List.map (Atom.rename .refl) p = p
      rw [show Atom.rename (n := n) .refl = id from funext ih, List.map_id]
    have hk (k : Key n) : k.rename .refl = k := by
      cases k
      simp [Key.rename, hp]
    have hr (rs : List (Key n × Profile n)) : Rows.rename .refl rs = rs := by
      simp [Rows.rename, hk, hp]
    cases atom with
    | sort => rfl
    | pad atom => simp only [rename_pad, ih]
    | fn => simp only [rename_fn, hk, ih]
    | pi A B domain rows =>
      simp only [rename_pi, VExpr.lift'_refl, hp, hr,
        VExpr.lift'_depth_zero (show Lift.depth (.cons .refl) = 0 from rfl)]
    | family data =>
      rw [rename_family, show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => VExpr.lift'_refl),
        show Profile.rename (n := n) .refl = id from funext hp, FamilyData.map_id]
    | ctor data =>
      rw [rename_ctor, show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => VExpr.lift'_refl),
        show Profile.rename (n := n) .refl = id from funext hp, ConstructorData.map_id]
    | record data =>
      rw [rename_record, show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => VExpr.lift'_refl),
        show Profile.rename (n := n) .refl = id from funext hp, RecordData.map_id]

@[simp] theorem Profile.rename_refl (profile : Profile n) : profile.rename .refl = profile := by
  change List.map (Atom.rename .refl) profile = profile
  rw [show Atom.rename (n := n) .refl = id from funext Atom.rename_refl, List.map_id]

@[simp] theorem Key.rename_refl (key : Key n) : key.rename .refl = key := by
  cases key
  simp [Key.rename]

theorem Atom.rename_comp (atom : Atom n) (ρ τ : Lift) :
    atom.rename (ρ.comp τ) = (atom.rename ρ).rename τ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp (p : Profile n) : p.rename (ρ.comp τ) = (p.rename ρ).rename τ := by
      change List.map _ p = List.map _ (List.map _ p)
      rw [List.map_map]
      exact List.map_congr_left fun a _ => ih a
    have hk (k : Key n) : k.rename (ρ.comp τ) = (k.rename ρ).rename τ := by
      cases k
      simp [Key.rename, hp, VExpr.lift'_comp]
    have hr (rs : List (Key n × Profile n)) :
        Rows.rename (ρ.comp τ) rs = Rows.rename τ (Rows.rename ρ rs) := by
      simp [Rows.rename, List.map_map, hk, hp]
    cases atom with
    | sort => rfl
    | pad atom => simp only [rename_pad, ih]
    | fn => simp only [rename_fn, hk, ih]
    | pi => simp only [rename_pi, hp, hr, show (ρ.comp τ).cons = ρ.cons.comp τ.cons from rfl,
        VExpr.lift'_comp]
    | family data =>
      simp only [rename_family, FamilyData.map_map]
      congr 2
      · funext e; exact VExpr.lift'_comp
      · funext p; exact hp p
    | ctor data =>
      simp only [rename_ctor, ConstructorData.map_map]
      congr 2
      · funext e; exact VExpr.lift'_comp
      · funext p; exact hp p
    | record data =>
      simp only [rename_record, RecordData.map_map]
      congr 2
      · funext e; exact VExpr.lift'_comp
      · funext p; exact hp p

theorem Profile.rename_comp (profile : Profile n) (ρ τ : Lift) :
    profile.rename (ρ.comp τ) = (profile.rename ρ).rename τ := by
  change List.map _ profile = List.map _ (List.map _ profile)
  rw [List.map_map]
  exact List.map_congr_left fun a _ => Atom.rename_comp a ρ τ

theorem Key.rename_comp (key : Key n) (ρ τ : Lift) :
    key.rename (ρ.comp τ) = (key.rename ρ).rename τ := by
  cases key
  simp [Key.rename, Profile.rename_comp, VExpr.lift'_comp]

theorem Atom.rename_injective (ρ : Lift) : Function.Injective (Atom.rename (n := n) ρ) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    have hp {p q : Profile n} : p.rename ρ = q.rename ρ ↔ p = q :=
      List.map_inj_right (fun _ _ h => ih h)
    have hk {k l : Key n} : k.rename ρ = l.rename ρ ↔ k = l := by
      cases k
      cases l
      simp [Key.rename, KeyData.mk.injEq, VExpr.lift'_inj, hp]
    have hr {rs ss : List (Key n × Profile n)} :
        Rows.rename ρ rs = Rows.rename ρ ss ↔ rs = ss := by
      apply List.map_inj_right
      intro a b h
      cases a
      cases b
      simpa [Prod.mk.injEq, hk, hp] using h
    intro a b h
    cases a <;> cases b <;>
      simp only [Atom.rename_sort, Atom.rename_fn, Atom.rename_pi, Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record] at h
    all_goals try (solve | cases h <;> rfl)
    · injection h with h₁ h₂
      cases hk.mp h₁
      cases ih h₂
      rfl
    · injection h with h₁ h₂ h₃ h₄
      cases VExpr.lift'_inj.mp h₁
      cases VExpr.lift'_inj.mp h₂
      cases hp.mp h₃
      cases hr.mp h₄
      rfl
    · injection h with he
      cases ih he
      rfl
    · injection h with equal
      exact congrArg AtomData.family (FamilyData.map_injective
        (fun _ _ h => VExpr.lift'_inj.mp h) (fun _ _ h => hp.mp h) equal)
    · injection h with equal
      exact congrArg AtomData.ctor (ConstructorData.map_injective
        (fun _ _ h => VExpr.lift'_inj.mp h) (fun _ _ h => hp.mp h) equal)
    · injection h with equal
      exact congrArg AtomData.record (RecordData.map_injective
        (fun _ _ h => VExpr.lift'_inj.mp h) (fun _ _ h => hp.mp h) equal)

@[simp] theorem Profile.rename_inj {left right : Profile n} :
    left.rename ρ = right.rename ρ ↔ left = right :=
  List.map_inj_right (fun _ _ h => Atom.rename_injective ρ h)

@[simp] theorem Key.rename_inj {left right : Key n} :
    left.rename ρ = right.rename ρ ↔ left = right := by
  cases left
  cases right
  simp [Key.rename, KeyData.mk.injEq, VExpr.lift'_inj]

private theorem rowsLE_rename (ρ : Lift)
    (ih : ∀ left right : Profile n,
      (checks n).le (left.rename ρ) (right.rename ρ) ↔ (checks n).le left right)
    (left right : List (Key n × Profile n)) :
    RowsLE (checks n) (Rows.rename ρ left) (Rows.rename ρ right) ↔
      RowsLE (checks n) left right := by
  constructor
  · intro h key output hm
    obtain ⟨other, ho, hle⟩ := h (key.rename ρ) (output.rename ρ)
      (List.mem_map.mpr ⟨(key, output), hm, rfl⟩)
    obtain ⟨⟨key', output'⟩, hr, he⟩ := List.mem_map.mp ho
    have he := Prod.mk.inj he
    have hkey := Key.rename_inj.mp he.1
    cases hkey
    cases he.2
    exact ⟨output', hr, (ih _ _).mp hle⟩
  · intro h key output hm
    obtain ⟨⟨key', output'⟩, hl, he⟩ := List.mem_map.mp hm
    cases he
    obtain ⟨other, ho, hle⟩ := h key' output' hl
    exact ⟨other.rename ρ, List.mem_map.mpr ⟨(key', other), ho, rfl⟩,
      (ih _ _).mpr hle⟩

private theorem checks_rename (ρ : Lift) :
    (∀ left right : Profile n,
      (checks n).le (left.rename ρ) (right.rename ρ) ↔ (checks n).le left right) ∧
    (∀ profile : Profile n, (checks n).wf (profile.rename ρ) ↔ (checks n).wf profile) ∧
    (∀ value type : Profile n,
      (checks n).typed (value.rename ρ) (type.rename ρ) ↔ (checks n).typed value type) := by
  induction n with
  | zero =>
    have hp (p : Profile 0) : p.rename ρ = p := by
      change List.map id p = p
      exact List.map_id p
    simp only [hp, implies_true, and_self]
  | succ n ih =>
    have hfamily (a b : FamilyData (Profile n)) :
        a.map (·.lift' ρ) (Profile.rename ρ) = b.map (·.lift' ρ) (Profile.rename ρ) ↔ a = b :=
      ⟨fun equal => FamilyData.map_injective (fun _ _ h => VExpr.lift'_inj.mp h)
        (fun _ _ h => Profile.rename_inj.mp h) equal, fun h => congrArg _ h⟩
    have hctor (a b : ConstructorData (Profile n)) :
        a.map (·.lift' ρ) (Profile.rename ρ) = b.map (·.lift' ρ) (Profile.rename ρ) ↔ a = b :=
      ⟨fun equal => ConstructorData.map_injective (fun _ _ h => VExpr.lift'_inj.mp h)
        (fun _ _ h => Profile.rename_inj.mp h) equal, fun h => congrArg _ h⟩
    have hrecord (a b : RecordData (Profile n)) :
        a.map (·.lift' ρ) (Profile.rename ρ) = b.map (·.lift' ρ) (Profile.rename ρ) ↔ a = b :=
      ⟨fun equal => RecordData.map_injective (fun _ _ h => VExpr.lift'_inj.mp h)
        (fun _ _ h => Profile.rename_inj.mp h) equal, fun h => congrArg _ h⟩
    have hfamilyWF (data : FamilyData (Profile n)) :
        FamilyWF (checks n) (data.map (·.lift' ρ) (Profile.rename ρ)) ↔ FamilyWF (checks n) data := by
      simp only [FamilyWF, FamilyData.map, List.forall_mem_map, RequestWF, DataRequest.map, KeyData.map, ih.2.1]
    have hal (a b : Atom (n + 1)) :
        AtomLE (checks n) (a.rename ρ) (b.rename ρ) ↔ AtomLE (checks n) a b := by
      cases a <;> cases b <;>
        simp only [Atom.rename_sort, Atom.rename_fn, Atom.rename_pi, Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record, AtomLE,
          Key.rename_inj (n := n), VExpr.lift'_inj, ← Profile.rename_singleton,
          ih.1, rowsLE_rename ρ ih.1, hfamily, hctor, hrecord]
    have haw (a : Atom (n + 1)) :
        AtomWF (checks n) (a.rename ρ) ↔ AtomWF (checks n) a := by
      cases a with
      | sort => exact Iff.rfl
      | pad atom => simpa only [Atom.rename_pad, AtomWF, ← Profile.rename_singleton] using
          (ih.2.1 (.singleton atom))
      | fn key output =>
        simp only [Atom.rename_fn, AtomWF, KeyWF, Key.rename,
          ← Profile.rename_singleton, ih.2.1]
      | pi A B domain rows =>
        simp only [Atom.rename_pi, AtomWF]
        have hdomain : (checks n).typed (Profile.rename ρ domain) (Profile.sort true) ↔
            (checks n).typed domain (Profile.sort true) := by
          simpa only [Profile.rename_sort] using ih.2.2 domain (Profile.sort true)
        rw [hdomain]
        apply and_congr_right
        intro _
        constructor
        · intro h key output hm
          have h' := h (Key.rename ρ key) (Profile.rename ρ output)
            (List.mem_map.mpr ⟨(key, output), hm, rfl⟩)
          exact ⟨(ih.2.2 _ _).mp h'.1, (ih.2.1 _).mp h'.2⟩
        · intro h key output hm
          obtain ⟨⟨key', output'⟩, hsource, he⟩ := List.mem_map.mp hm
          cases he
          exact ⟨(ih.2.2 _ _).mpr (h _ _ hsource).1, (ih.2.1 _).mpr (h _ _ hsource).2⟩
      | family data => exact hfamilyWF data
      | ctor data =>
        simp only [Atom.rename_ctor, AtomWF, ConstructorWF, ConstructorData.map,
          hfamilyWF, List.forall_mem_map, RequestWF, DataRequest.map, KeyData.map, ih.2.1]
      | record data =>
        simp only [Atom.rename_record, AtomWF, RecordWF, RecordData.map,
          hfamilyWF, List.forall_mem_map, RequestWF, DataRequest.map, KeyData.map, ih.2.1]
    have hat (a b : Atom (n + 1)) :
        AtomTyped (checks n) (a.rename ρ) (b.rename ρ) ↔ AtomTyped (checks n) a b := by
      cases a <;> cases b <;>
        simp only [Atom.rename_sort, Atom.rename_fn, Atom.rename_pi, Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record, AtomTyped]
      · rename_i key output A B domain rows
        constructor
        · rintro ⟨type, hm, ht⟩
          obtain ⟨⟨key', type'⟩, hsource, he⟩ := List.mem_map.mp hm
          have he := Prod.mk.inj he
          cases Key.rename_inj.mp he.1
          cases he.2
          rw [← Profile.rename_singleton] at ht
          exact ⟨type', hsource, (ih.2.2 _ _).mp ht⟩
        · rintro ⟨type, hm, ht⟩
          refine ⟨Profile.rename ρ type, List.mem_map.mpr ⟨(key, type), hm, rfl⟩, ?_⟩
          rw [← Profile.rename_singleton]
          exact (ih.2.2 _ _).mpr ht
      · rename_i A B domain rows relevant
        constructor
        · intro h key output hm
          have ht := h (Key.rename ρ key) (Profile.rename ρ output)
            (List.mem_map.mpr ⟨(key, output), hm, rfl⟩)
          rw [← Profile.rename_sort (ρ := ρ) relevant] at ht
          exact (ih.2.2 _ _).mp ht
        · intro h key output hm
          obtain ⟨⟨key', output'⟩, hsource, he⟩ := List.mem_map.mp hm
          cases he
          rw [← Profile.rename_sort (ρ := ρ) relevant]
          exact (ih.2.2 _ _).mpr (h _ _ hsource)
      · simpa only [Profile.rename_singleton, Profile.rename_sort] using
          (ih.2.2 (.singleton _) (.sort _))
      · simpa only [← Profile.rename_singleton] using
          (ih.2.2 (.singleton _) (.singleton _))
      · rfl
      · exact hfamily _ _
      · exact hfamily _ _
    have hw (p : Profile (n + 1)) :
        (checks (n + 1)).wf (p.rename ρ) ↔ (checks (n + 1)).wf p := by
      change (∀ a ∈ List.map (Atom.rename ρ) p, AtomWF (checks n) a) ↔ _
      simp only [List.forall_mem_map, haw]
      rfl
    refine ⟨?_, hw, ?_⟩
    · intro left right
      change Covers (AtomLE (checks n)) (left.rename ρ) (right.rename ρ) ↔ _
      constructor
      · intro h a ha
        obtain ⟨b, hb, he⟩ := h (a.rename ρ) (List.mem_map.mpr ⟨a, ha, rfl⟩)
        obtain ⟨b, hsource, rfl⟩ := List.mem_map.mp hb
        exact ⟨b, hsource, (hal a b).mp he⟩
      · intro h a ha
        obtain ⟨a, hsource, rfl⟩ := List.mem_map.mp ha
        obtain ⟨b, hb, he⟩ := h a hsource
        exact ⟨b.rename ρ, List.mem_map.mpr ⟨b, hb, rfl⟩, (hal a b).mpr he⟩
    · intro value type
      change ((checks (n + 1)).wf (value.rename ρ) ∧
        (checks (n + 1)).wf (type.rename ρ) ∧
        ∀ a ∈ (value.rename ρ).atoms, ∃ b ∈ (type.rename ρ).atoms,
          AtomTyped (checks n) a b) ↔ _
      rw [hw, hw]
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      constructor
      · intro h a ha
        obtain ⟨b, hb, ht⟩ := h (a.rename ρ) (List.mem_map.mpr ⟨a, ha, rfl⟩)
        obtain ⟨b, hsource, rfl⟩ := List.mem_map.mp hb
        exact ⟨b, hsource, (hat a b).mp ht⟩
      · intro h a ha
        obtain ⟨a, hsource, rfl⟩ := List.mem_map.mp ha
        obtain ⟨b, hb, ht⟩ := h a hsource
        exact ⟨b.rename ρ, List.mem_map.mpr ⟨b, hb, rfl⟩, (hat a b).mpr ht⟩

@[simp] theorem Profile.rename_le_iff {left right : Profile n} :
    Profile.LE (left.rename ρ) (right.rename ρ) ↔ Profile.LE left right :=
  (checks_rename ρ).1 left right

@[simp] theorem Profile.rename_wf_iff {profile : Profile n} :
    (profile.rename ρ).WF ↔ profile.WF := (checks_rename ρ).2.1 profile

@[simp] theorem Profile.rename_hasType_iff {value type : Profile n} :
    (value.rename ρ).HasType (type.rename ρ) ↔ value.HasType type :=
  (checks_rename ρ).2.2 value type

end Renaming
end Lean4Lean.AnchoredProfiles
