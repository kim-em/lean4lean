import Lean4Lean.Theory.Typing.AnchoredDataIntrinsic

/-! Finite hereditary typing supports. Each candidate retains the actual
finite constructor tree selecting its covers; no semantic relation occurs
in this producer. -/

namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

mutual
  /-- One selected cover for each atom of a finite value demand. -/
  inductive Minimal : {n : Nat} → Profile n → Profile n → Prop where
    | nil : Minimal (.empty : Profile n) .empty
    | cons : AtomMinimal atom first → Minimal rest tail →
        Minimal ((Profile.singleton atom).union rest) (first.union tail)

  /-- Hereditary choices retain a single function key and recurse on its
  input and output. Direct sort covers need no further type observation. -/
  inductive AtomMinimal : {n : Nat} → Atom n → Profile n → Prop where
    | sort (h : (Profile.singleton atom).HasType (.sort relevant)) :
        AtomMinimal atom (.sort relevant)
    | family {atom : Atom (n + 1)} {data : FamilyData (Profile n)}
        (h : (Profile.singleton atom).HasType (.singleton (.family data))) :
        AtomMinimal atom (.singleton (.family data))
    | fn {key : Key n} {output : Atom n} :
        Minimal key.input domain → Minimal (.singleton output) result →
        domain.HasType (.sort true) →
        AtomMinimal (n := n + 1) (.fn key output) (.pi A B domain [(key, result)])
    | pad {atom : Atom n} {support : Profile n} : Minimal (.singleton atom) support →
        AtomMinimal (n := n + 1) (.pad atom) support.pad
end

private structure Candidate (value bound : Profile n) where
  support : Profile n
  typed : value.HasType support
  dominated : support ≤ bound
  minimal : Minimal value support

private structure AtomCandidate (atom : Atom n) (bound : Profile n) where
  support : Profile n
  typed : (Profile.singleton atom).HasType support
  dominated : support ≤ bound
  minimal : AtomMinimal atom support

private theorem empty_le (profile : Profile n) : Profile.empty ≤ profile := by
  cases n <;> exact fun _ h => nomatch h

private theorem singleton_le_of_mem {profile : Profile n} (h : atom ∈ profile.atoms) :
    Profile.singleton atom ≤ profile := by
  cases n <;> intro a ha
  all_goals
    cases List.mem_singleton.mp ha
    exact profile.le_refl _ h

private def AtomCandidate.weaken (candidate : AtomCandidate atom bound)
    (h : bound ≤ bound') : AtomCandidate atom bound' :=
  { candidate with dominated := Profile.le_trans candidate.dominated h }

private def Candidate.empty (bound : Profile n) : Candidate .empty bound where
  support := .empty
  typed := .empty Profile.WF.empty
  dominated := empty_le bound
  minimal := .nil

private def Candidate.cons (first : AtomCandidate atom bound)
    (tail : Candidate rest bound) : Candidate ((Profile.singleton atom).union rest) bound where
  support := first.support.union tail.support
  typed := first.typed.union_types tail.typed
  dominated := Profile.union_le first.dominated tail.dominated
  minimal := .cons first.minimal tail.minimal

private noncomputable def zeroChoices (atom type : Atom 0) :
    List (AtomCandidate atom (.singleton type)) := by
  classical
  exact if h : (Profile.singleton atom).HasType (.singleton type) then
    [{ support := .singleton type, typed := h,
       dominated := Profile.le_refl _, minimal := .sort h }]
    else []

private def fnCandidate {key : Key n} {output : Atom n}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (hw : (Profile.pi A B domain rows).WF) (hm : (key, result) ∈ rows)
    (input : Candidate key.input domain) (body : Candidate (.singleton output) result) :
    AtomCandidate (n := n + 1) (.fn key output) (.pi A B domain rows) := by
  have hd : input.support.HasType (.sort true) :=
    (Profile.WF.pi_iff.mp hw).1.restrict input.dominated input.typed.wf_type
  have hpi : (Profile.pi A B input.support [(key, body.support)]).WF := by
    apply Profile.WF.pi_iff.mpr
    refine ⟨hd, ?_⟩
    intro k b h
    cases List.mem_singleton.mp h
    exact ⟨input.typed, body.typed.wf_type⟩
  refine {
    support := .pi A B input.support [(key, body.support)]
    typed := Profile.HasType.fn hpi (List.mem_singleton_self _) body.typed
    dominated := Profile.pi_le_pi_iff.mpr ⟨input.dominated, ?_⟩
    minimal := .fn input.minimal body.minimal hd }
  intro k b h
  cases List.mem_singleton.mp h
  exact ⟨result, hm, body.dominated⟩

private def padCandidate {atom type : Atom n}
    (candidate : Candidate (.singleton atom) (.singleton type)) :
    AtomCandidate (n := n + 1) (.pad atom) (.singleton (.pad type)) where
  support := candidate.support.pad
  typed := candidate.typed.pad
  dominated := candidate.dominated.pad
  minimal := .pad candidate.minimal

private noncomputable def successorChoices
    (lower : (value bound : Profile n) → List (Candidate value bound))
    (atom type : Atom (n + 1)) : List (AtomCandidate atom (.singleton type)) := by
  classical
  exact match atom, type with
  | atom, .sort relevant =>
      if h : (Profile.singleton atom).HasType (.sort relevant) then
        [{ support := .sort relevant, typed := h,
           dominated := Profile.le_refl _, minimal := .sort h }]
      else []
  | atom, .family data =>
      if h : (Profile.singleton atom).HasType (.singleton (.family data)) then
        [{ support := .singleton (.family data), typed := h,
           dominated := Profile.le_refl _, minimal := .family h }]
      else []
  | .fn key output, .pi A B domain rows =>
      if hw : (Profile.pi A B domain rows).WF then
        rows.attach.flatMap fun row =>
          if he : row.val.1 = key then
            (lower key.input domain).flatMap fun input =>
              (lower (.singleton output) row.val.2).map fun body =>
                fnCandidate hw (by
                  have hp : row.val = (key, row.val.2) := Prod.ext he rfl
                  exact hp ▸ row.property) input body
          else []
      else []
  | .pad atom, .pad type =>
      (lower (.singleton atom) (.singleton type)).map padCandidate
  | _, _ => []

private noncomputable def assemble
    (choices : (atom type : Atom n) → List (AtomCandidate atom (.singleton type)))
    (bound : Profile n) : (value : Profile n) → List (Candidate value bound)
  | [] => [Candidate.empty bound]
  | atom :: rest =>
      bound.attach.flatMap fun type =>
        (choices atom type.val).flatMap fun first =>
          (assemble choices bound rest).map fun tail =>
            Candidate.cons (first.weaken (singleton_le_of_mem type.property)) tail

private noncomputable def candidates : (n : Nat) →
    (value bound : Profile n) → List (Candidate value bound)
  | 0, value, bound => assemble zeroChoices bound value
  | n + 1, value, bound => assemble (successorChoices (candidates n)) bound value

private theorem wf_singleton {profile : Profile n} (hw : profile.WF)
    (hm : atom ∈ profile.atoms) : (Profile.singleton atom).WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro a ha
    cases List.mem_singleton.mp ha
    exact hw _ hm

private theorem typed_cover {value type : Profile n} (h : value.HasType type)
    (hm : atom ∈ value.atoms) :
    ∃ other ∈ type.atoms, (Profile.singleton atom).HasType (.singleton other) := by
  cases n with
  | zero =>
    obtain ⟨other, ho, ht⟩ := h _ hm
    exact ⟨other, ho, fun _ _ => ⟨other, List.mem_singleton_self _, ht⟩⟩
  | succ n =>
    obtain ⟨other, ho, ht⟩ := h.2.2 _ hm
    refine ⟨other, ho, wf_singleton h.wf_value hm, wf_singleton h.wf_type ho, ?_⟩
    intro a ha
    cases List.mem_singleton.mp ha
    exact ⟨other, List.mem_singleton_self _, ht⟩

private theorem typed_tail {atom : Atom n} {rest bound : Profile n}
    (h : Profile.HasType (atom :: rest) bound) : rest.HasType bound := by
  cases n with
  | zero => exact fun a ha => h a (List.mem_cons_of_mem _ ha)
  | succ n => exact ⟨fun a ha => h.1 a (List.mem_cons_of_mem _ ha),
      h.2.1, fun a ha => h.2.2 a (List.mem_cons_of_mem _ ha)⟩

private theorem assemble_exists
    (choices : (atom type : Atom n) → List (AtomCandidate atom (.singleton type)))
    (complete : ∀ atom type, (Profile.singleton atom).HasType (.singleton type) →
      ∃ c, c ∈ choices atom type)
    {value bound : Profile n} (h : value.HasType bound) :
    ∃ c, c ∈ assemble choices bound value := by
  induction value with
  | nil => exact ⟨_, List.mem_singleton_self _⟩
  | cons atom rest ih =>
    obtain ⟨type, ht, htyped⟩ := typed_cover h List.mem_cons_self
    obtain ⟨first, hf⟩ := complete atom type htyped
    obtain ⟨tail, htail⟩ := ih (typed_tail h)
    exact ⟨_, List.mem_flatMap.mpr ⟨⟨type, ht⟩, List.mem_attach _ _,
      List.mem_flatMap.mpr ⟨first, hf, List.mem_map.mpr ⟨tail, htail, rfl⟩⟩⟩⟩

private theorem zeroChoices_exists {atom type : Atom 0}
    (h : (Profile.singleton atom).HasType (.singleton type)) :
    ∃ c, c ∈ zeroChoices atom type := by
  classical
  simp only [zeroChoices, dif_pos h]
  exact ⟨_, List.mem_singleton_self _⟩

private theorem successorChoices_exists
    (lower : (value bound : Profile n) → List (Candidate value bound))
    (complete : ∀ {value bound}, value.HasType bound → ∃ c, c ∈ lower value bound)
    {atom type : Atom (n + 1)}
    (h : (Profile.singleton atom).HasType (.singleton type)) :
    ∃ c, c ∈ successorChoices lower atom type := by
  classical
  obtain ⟨other, hm, ht⟩ := h.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp hm
  cases type with
  | sort relevant =>
    change (Profile.singleton atom).HasType (.sort relevant) at h
    simp only [successorChoices, dif_pos h]
    exact ⟨_, List.mem_singleton_self _⟩
  | fn | ctor | record => cases atom <;> contradiction
  | family data =>
    simp only [successorChoices, dif_pos h]
    exact ⟨_, List.mem_singleton_self _⟩
  | pad type =>
    cases atom with
    | pad atom =>
      obtain ⟨c, hc⟩ := complete ht
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩⟩
    | sort | family | ctor | record => contradiction
    | fn => contradiction
    | pi => contradiction
  | pi A B domain rows =>
    cases atom with
    | fn key output =>
      obtain ⟨result, hr, ho⟩ := ht
      have hw : (Profile.pi A B domain rows).WF := h.wf_type
      have hi := ((Profile.WF.pi_iff.mp hw).2 _ _ hr).1
      obtain ⟨input, hinput⟩ := complete hi
      obtain ⟨body, hbody⟩ := complete ho
      simp only [successorChoices, dif_pos hw]
      refine ⟨fnCandidate hw hr input body,
        List.mem_flatMap.mpr ⟨⟨(key, result), hr⟩, List.mem_attach _ _, ?_⟩⟩
      simp only
      exact List.mem_flatMap.mpr ⟨input, hinput, List.mem_map.mpr ⟨body, hbody, rfl⟩⟩
    | sort | family | ctor | record => contradiction
    | pi => contradiction
    | pad => contradiction

private theorem candidates_exists {value bound : Profile n} (h : value.HasType bound) :
    ∃ c, c ∈ candidates n value bound := by
  induction n with
  | zero => exact assemble_exists zeroChoices (fun _ _ => zeroChoices_exists) h
  | succ n ih =>
    exact assemble_exists (successorChoices (candidates n))
      (fun _ _ => successorChoices_exists (candidates n) (fun h => ih h)) h

/-- The finite list of hereditary supports selected from the given bound. -/
noncomputable def Basis (value bound : Profile n) : List (Profile n) :=
  (candidates n value bound).map (·.support)

/-- Supports for a single selected atom and a single covering atom. -/
noncomputable def Basis.choices : (n : Nat) → Atom n → Atom n → List (Profile n)
  | 0, atom, type => (zeroChoices atom type).map (·.support)
  | n + 1, atom, type => (successorChoices (candidates n) atom type).map (·.support)

private theorem attach_flatMap (xs : List α) (f : α → List β) :
    xs.attach.flatMap (fun x => f x.val) = xs.flatMap f := by
  rw [← List.flatMap_map]
  simp

theorem Basis.nil (bound : Profile n) : Basis Profile.empty bound = [Profile.empty] := by
  cases n <;> rfl

theorem Basis.cons (atom : Atom n) (rest bound : Profile n) :
    Basis (atom :: rest) bound = bound.flatMap fun type =>
      (Basis.choices n atom type).flatMap fun first =>
        (Basis rest bound).map (first.union ·) := by
  cases n <;>
    simp only [Basis, candidates, assemble, Basis.choices, List.map_flatMap, List.map_map,
      List.flatMap_map, Function.comp_def, Candidate.cons, AtomCandidate.weaken]
  · exact attach_flatMap bound (fun type => (zeroChoices atom type).flatMap fun first =>
      (assemble zeroChoices bound rest).map fun tail => first.support.union tail.support)
  · exact attach_flatMap bound (fun type => (successorChoices (candidates _) atom type).flatMap fun first =>
      (assemble (successorChoices (candidates _)) bound rest).map fun tail => first.support.union tail.support)

open Classical in
theorem Basis.choices_zero (atom type : Atom 0) :
    Basis.choices 0 atom type =
      if (Profile.singleton atom).HasType (.singleton type) then [Profile.singleton type] else [] := by
  classical
  simp only [Basis.choices, zeroChoices]
  split <;> rfl

open Classical in
theorem Basis.choices_succ (atom type : Atom (n + 1)) :
    Basis.choices (n + 1) atom type =
      match atom, type with
      | atom, .sort relevant =>
          if (Profile.singleton atom).HasType (.sort relevant) then [Profile.sort relevant] else []
      | atom, .family data =>
          if (Profile.singleton atom).HasType (.singleton (.family data)) then
            [Profile.singleton (.family data)] else []
      | .fn key output, .pi A B domain rows =>
          if (Profile.pi A B domain rows).WF then
            rows.flatMap fun row => if row.1 = key then
              (Basis key.input domain).flatMap fun input =>
                (Basis (.singleton output) row.2).map fun body =>
                  .pi A B input [(key, body)]
            else []
          else []
      | .pad atom, .pad type => (Basis (.singleton atom) (.singleton type)).map Profile.pad
      | _, _ => [] := by
  classical
  cases atom <;> cases type <;>
    simp only [Basis.choices, successorChoices, List.map_nil]
  all_goals first
    | (split <;> rfl)
    | (simp only [Basis, List.map_map]; rfl)
    | rfl
    | skip
  rename_i key output A B domain rows
  split
  · rename_i hw
    simp only [List.map_flatMap, Basis, List.flatMap_map, List.map_map, Function.comp_def]
    have h (row : {r // r ∈ rows}) :
        List.map (fun x => x.support)
          (if he : row.val.1 = key then
            (candidates _ key.input domain).flatMap fun input =>
              (candidates _ (.singleton output) row.val.2).map fun body =>
                fnCandidate hw (by have hp : row.val = (key, row.val.2) := Prod.ext he rfl; exact hp ▸ row.property) input body
            else []) =
          (if row.val.1 = key then
            (candidates _ key.input domain).flatMap fun input =>
              (candidates _ (.singleton output) row.val.2).map fun body =>
                Profile.pi A B input.support [(key, body.support)] else []) := by
      split <;> simp only [List.map_flatMap, List.map_map, Function.comp_def, fnCandidate, List.map_nil]
    refine Eq.trans ?_ (attach_flatMap rows (fun row =>
      if row.1 = key then
        (candidates _ key.input domain).flatMap fun input =>
          (candidates _ (.singleton output) row.2).map fun body =>
            Profile.pi A B input.support [(key, body.support)] else []))
    apply congrArg (fun f => rows.attach.flatMap f)
    funext row
    exact h row
  · rfl

theorem Basis.valid {value bound : Profile n} (h : support ∈ Basis value bound) :
    value.HasType support ∧ support ≤ bound := by
  obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp h
  exact ⟨candidate.typed, candidate.dominated⟩

theorem Basis.minimal {value bound : Profile n} (h : support ∈ Basis value bound) :
    Minimal value support := by
  obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp h
  exact candidate.minimal

theorem Basis.exists {value bound : Profile n} (h : value.HasType bound) :
    ∃ support, support ∈ Basis value bound := by
  obtain ⟨candidate, hc⟩ := candidates_exists h
  exact ⟨candidate.support, List.mem_map.mpr ⟨candidate, hc, rfl⟩⟩

theorem Minimal.typed {value support : Profile n} (h : Minimal value support) :
    value.HasType support := by
  induction h using Minimal.rec
      (motive_2 := fun atom support _ => (Profile.singleton atom).HasType support) with
  | nil => exact .empty .empty
  | cons first tail ihfirst ihtail => exact ihfirst.union_types ihtail
  | sort ht => exact ht
  | family ht => exact ht
  | @fn n domain result A B key output hi ho hd hinput houtput =>
    have hpi : (Profile.pi A B domain [(key, result)]).WF := by
      apply Profile.WF.pi_iff.mpr
      refine ⟨hd, ?_⟩
      intro k b hm
      cases List.mem_singleton.mp hm
      exact ⟨hinput, houtput.wf_type⟩
    exact Profile.HasType.fn hpi (List.mem_singleton_self _) houtput
  | pad lower ih => simpa only [Profile.pad_singleton] using ih.pad

theorem AtomMinimal.typed {atom : Atom n} {support : Profile n}
    (h : AtomMinimal atom support) : (Profile.singleton atom).HasType support := by
  have hp := (Minimal.cons h Minimal.nil).typed
  simpa only [Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using hp

/-- Every hereditary support is itself an intrinsically formed type profile. -/
theorem Minimal.formation {value support : Profile n} (h : Minimal value support) :
    support.HasType (.sort true) := by
  induction h using Minimal.rec
      (motive_2 := fun _ support _ => support.HasType (.sort true)) with
  | nil => exact .empty (Profile.WF.sort true)
  | cons first tail ihfirst ihtail => exact ihfirst.union ihtail
  | sort ht => exact Profile.HasType.sort _
  | family ht => exact ht.family_cover_formation
  | @fn n domain result A B key output hi ho hd hinput houtput =>
    apply Profile.HasType.pi_iff.mpr
    refine ⟨Profile.WF.pi_iff.mpr ⟨hd, ?_⟩, ?_⟩
    · intro k b hm
      cases List.mem_singleton.mp hm
      exact ⟨hi.typed, houtput.wf_value⟩
    · intro k b hm
      cases List.mem_singleton.mp hm
      exact houtput
  | pad lower ih => exact ih.pad_sort

theorem AtomMinimal.formation {atom : Atom n} {support : Profile n}
    (h : AtomMinimal atom support) : support.HasType (.sort true) := by
  have hp := (Minimal.cons h Minimal.nil).formation
  simpa only [Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using hp

/-- A selected part is contained by literal atom membership, not merely by
the refinement order. This retains its whole finite interpretation. -/
theorem Minimal.support_origin_subset {value support : Profile n}
    (h : Minimal value support) (hm : typeAtom ∈ support.atoms) :
    ∃ atom ∈ value.atoms, ∃ part, AtomMinimal atom part ∧
      typeAtom ∈ part.atoms ∧ ∀ a ∈ part.atoms, a ∈ support.atoms := by
  induction value generalizing support with
  | nil =>
    cases h with
    | nil => cases hm
  | cons atom value ih =>
    cases h with
    | @cons _ _ first _ tail hfirst htail =>
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨atom, List.mem_cons_self, first, hfirst, hm,
          fun _ ha => List.mem_append.mpr (.inl ha)⟩
      · obtain ⟨a, ha, part, hp, ht, hsubset⟩ := ih htail hm
        exact ⟨a, List.mem_cons_of_mem _ ha, part, hp, ht,
          fun x hx => List.mem_append.mpr (.inr (hsubset x hx))⟩

/-- Every atom of the selected support comes from one demanded value atom.
This is the direction required to interpret all atoms of that support. -/
theorem Minimal.support_origin {value support : Profile n} (h : Minimal value support)
    (hm : typeAtom ∈ support.atoms) :
    ∃ atom ∈ value.atoms, ∃ part, AtomMinimal atom part ∧ typeAtom ∈ part.atoms := by
  obtain ⟨atom, ha, part, hp, ht, _⟩ := h.support_origin_subset hm
  exact ⟨atom, ha, part, hp, ht⟩

/-- Each demanded atom has one hereditary cover contained in the finite
union. This direction does not assert semantic restriction. -/
theorem Minimal.cover {value support : Profile n} (h : Minimal value support)
    (hm : atom ∈ value.atoms) :
    ∃ part, AtomMinimal atom part ∧ part ≤ support := by
  induction value generalizing support with
  | nil => cases hm
  | cons head value ih =>
    cases h with
    | @cons _ _ first _ tail hfirst htail =>
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        exact ⟨first, hfirst, Profile.le_union_left first tail⟩
      · obtain ⟨part, hp, hle⟩ := ih htail hm
        exact ⟨part, hp, Profile.le_trans hle (Profile.le_union_right first tail)⟩

theorem AtomMinimal.fn_inv {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (h : AtomMinimal (n := n + 1) (.fn key output) support) :
    ∃ A B domain result,
      support = Profile.pi A B domain [(key, result)] ∧
      Minimal key.input domain ∧ Minimal (.singleton output) result ∧
      domain.HasType (.sort true) := by
  cases h with
  | sort ht =>
    obtain ⟨_, _, _, _, _, hm, _⟩ := ht.fn_inv (List.mem_singleton_self _)
    cases List.mem_singleton.mp hm
  | family ht =>
    obtain ⟨_, _, _, _, _, hm, _⟩ := ht.fn_inv (List.mem_singleton_self _)
    cases List.mem_singleton.mp hm
  | fn hi ho hd => exact ⟨_, _, _, _, rfl, hi, ho, hd⟩

theorem Minimal.rename {value support : Profile n} (h : Minimal value support)
    (ρ : Lift) : Minimal (value.rename ρ) (support.rename ρ) := by
  induction h using Minimal.rec
      (motive_2 := fun atom support _ => AtomMinimal (atom.rename ρ) (support.rename ρ)) with
  | nil => exact .nil
  | cons first tail ihfirst ihtail =>
    simpa only [Profile.rename_union, Profile.rename_singleton] using
      Minimal.cons ihfirst ihtail
  | sort ht =>
    rw [Profile.rename_sort]
    apply AtomMinimal.sort
    simpa only [Profile.rename_singleton, Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr ht
  | @family n atom data ht =>
    apply AtomMinimal.family
    have shifted := (Profile.rename_hasType_iff (ρ := ρ)).mpr ht
    simp only [Profile.rename_singleton, Atom.rename_family] at shifted
    rw [show @Profile.rename n ρ = List.map (Atom.rename ρ) from rfl] at shifted
    exact shifted
  | @fn n domain result A B key output hi ho hd hinput houtput =>
    have hdomain := (Profile.rename_hasType_iff (ρ := ρ)).mpr hd
    rw [Profile.rename_sort] at hdomain
    simp only [Profile.rename_singleton] at houtput
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Rows.rename, List.map_cons, List.map_nil, Key.rename] using
      AtomMinimal.fn (key := key.rename ρ) (A := A.lift' ρ) (B := B.lift' ρ.cons)
        hinput houtput hdomain
  | pad lower ih =>
    simp only [Profile.rename_singleton] at ih
    simpa only [Atom.rename_pad, Profile.rename_pad] using AtomMinimal.pad ih

theorem AtomMinimal.rename {atom : Atom n} {support : Profile n}
    (h : AtomMinimal atom support) (ρ : Lift) :
    AtomMinimal (atom.rename ρ) (support.rename ρ) := by
  cases h with
  | sort ht =>
    rw [Profile.rename_sort]
    apply AtomMinimal.sort
    simpa only [Profile.rename_singleton, Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr ht
  | @family n atom data ht =>
    apply AtomMinimal.family
    have shifted := (Profile.rename_hasType_iff (ρ := ρ)).mpr ht
    simp only [Profile.rename_singleton, Atom.rename_family] at shifted
    rw [show @Profile.rename n ρ = List.map (Atom.rename ρ) from rfl] at shifted
    exact shifted
  | @fn n domain result A B key output hi ho hd =>
    have hinput := Minimal.rename hi ρ
    have houtput := Minimal.rename ho ρ
    have hdomain := (Profile.rename_hasType_iff (ρ := ρ)).mpr hd
    rw [Profile.rename_sort] at hdomain
    simp only [Profile.rename_singleton] at houtput
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Rows.rename, List.map_cons, List.map_nil, Key.rename] using
      AtomMinimal.fn (key := key.rename ρ) (A := A.lift' ρ) (B := B.lift' ρ.cons)
        hinput houtput hdomain
  | pad lower =>
    have ih := Minimal.rename lower ρ
    simp only [Profile.rename_singleton] at ih
    simpa only [Atom.rename_pad, Profile.rename_pad] using AtomMinimal.pad ih

end Lean4Lean.AnchoredProfiles
