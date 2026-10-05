import Lean4Lean.Theory.Typing.AnchoredInputExtension

/-! Finite adapters in hereditary normal form. Function inputs are
contravariant and outputs covariant. No intermediate type capability is
stored by composition. These are syntax and guards, not an interpreter. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- An unchanged input inherits the old function's anchor admission. A new
input retains the concrete admission which justified introducing that row. -/
inductive AdapterSeed (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (key : Key n) : Profile n → Type where
  | same : AdapterSeed env U registry Γ key key.input
  | supplied {input : Profile n}
      (admitted : Admitted env U registry Γ (inputKey key input) key.anchor key.anchor) :
      AdapterSeed env U registry Γ key input
  | view {middle input : Profile n}
      (previous : AdapterSeed env U registry Γ key middle)
      (change : ProfileView env U registry Γ middle input) :
      AdapterSeed env U registry Γ key input

def AdapterSeed.comp
    (first : AdapterSeed env U registry Γ key middle)
    (second : AdapterSeed env U registry Γ (inputKey key middle) last) :
    AdapterSeed env U registry Γ key last := by
  match second with
  | .same => exact first
  | .supplied admitted => exact .supplied admitted
  | .view previous change => exact .view (first.comp previous) change
termination_by sizeOf second
decreasing_by simp_wf; omega

noncomputable def AdapterSeed.future (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (seed : AdapterSeed env U registry Γ key input) :
    AdapterSeed env U registry Δ (key.rename ρ) (input.rename ρ) := by
  match seed with
  | .same => exact .same
  | .supplied admitted => exact .supplied (Admitted.future henv W admitted)
  | .view previous change => exact .view (previous.future henv W) (change.future henv W)
termination_by sizeOf seed
decreasing_by simp_wf; omega

mutual
inductive AtomAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Atom n → Atom n → Type where
  | refl (atom : Atom n) : AtomAdapter env U registry Γ atom atom
  | fn {key newKey : Key n} {output output' : Atom n}
      (keys : KeyProgram env U registry Γ key newKey)
      (result : AtomAdapter env U registry Γ output output') :
      AtomAdapter env U registry Γ (n := n + 1) (.fn key output) (.fn newKey output')
  | pad {atom atom' : Atom n} (adapter : AtomAdapter env U registry Γ atom atom') :
      AtomAdapter env U registry Γ (n := n + 1) (.pad atom) (.pad atom')

/-- Every output atom names an actual input origin. Unused input atoms may be
discarded and the same input origin may be used more than once. -/
inductive ProfileAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Profile n → Profile n → Type where
  | nil (source : Profile n) : ProfileAdapter env U registry Γ source []
  | cons {source target : Profile n} {atom output : Atom n}
      (member : atom ∈ source.atoms)
      (head : AtomAdapter env U registry Γ atom output)
      (tail : ProfileAdapter env U registry Γ source target) :
      ProfileAdapter env U registry Γ source (output :: target)

/-- Key programs operate on admissions at the rank below a function atom.
Their intermediate guards are concrete; they request no intermediate
function type capability. -/
inductive KeyProgram (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Key n → Key n → Type where
  | refl (key : Key n) : KeyProgram env U registry Γ key key
  | input {key : Key n} {input : Profile n}
      (seed : AdapterSeed env U registry Γ key input)
      (arguments : ProfileAdapter env U registry Γ input key.input) :
      KeyProgram env U registry Γ key (inputKey key input)
  | reanchor {key : Key n} {anchor : VExpr}
      (admitted : Admitted env U registry Γ key anchor anchor) :
      KeyProgram env U registry Γ key (reanchorKey key anchor)
  | domainRekey {key : Key n} {newDomain : VExpr} {guard : Profile n}
      (path : TypeConversion env U Γ key.domain newDomain)
      (typed : key.input.HasType guard) (formed : guard.HasType (.sort true))
      (bridge : TypeRelated env U registry Γ key.domain newDomain guard) :
      KeyProgram env U registry Γ key (domainKey key newDomain)
  | comp {first middle last : Key n}
      (left : KeyProgram env U registry Γ first middle)
      (right : KeyProgram env U registry Γ middle last) :
      KeyProgram env U registry Γ first last
end

theorem ProfileAdapter.origin
    (adapter : ProfileAdapter env U registry Γ source target)
    (member : atom ∈ target.atoms) :
    ∃ original, original ∈ source.atoms ∧
      Nonempty (AtomAdapter env U registry Γ original atom) := by
  match adapter with
  | .nil _ => cases member
  | .cons sourceMember head tail =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, sourceMember, ⟨head⟩⟩
    · exact tail.origin member
termination_by sizeOf adapter
decreasing_by simp_wf; omega

def ProfileAdapter.refl (source : Profile n) :
    ProfileAdapter env U registry Γ source source := by
  let rec go (target : Profile n) (included : List.Subset target source) :
      ProfileAdapter env U registry Γ source target :=
    match target with
    | [] => .nil source
    | atom :: tail => .cons (included List.mem_cons_self) (.refl atom)
        (go tail (fun _ hm => included (List.mem_cons_of_mem _ hm)))
  exact go source (fun _ h => h)

noncomputable def ProfileAdapter.select (included : List.Subset target source) :
    ProfileAdapter env U registry Γ source target := by
  induction target with
  | nil => exact .nil source
  | cons atom tail ih =>
    exact .cons (included List.mem_cons_self) (.refl atom)
      (ih (fun _ hm => included (List.mem_cons_of_mem _ hm)))

mutual
noncomputable def AtomAdapter.comp {a b c : Atom n}
    (first : AtomAdapter env U registry Γ a b)
    (second : AtomAdapter env U registry Γ b c) :
    AtomAdapter env U registry Γ a c := by
  match n, a, b, first with
  | _, _, _, .refl _ => exact second
  | _ + 1, _, _, .fn keys₁ result₁ =>
    match c, second with
    | _, .refl _ => exact .fn keys₁ result₁
    | _, .fn keys₂ result₂ => exact .fn (.comp keys₁ keys₂) (result₁.comp result₂)
  | _ + 1, _, _, .pad first =>
    match c, second with
    | _, .refl _ => exact .pad first
    | _, .pad second => exact .pad (first.comp second)
termination_by (2 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileAdapter.comp {source middle target : Profile n}
    (first : ProfileAdapter env U registry Γ source middle)
    (second : ProfileAdapter env U registry Γ middle target) :
    ProfileAdapter env U registry Γ source target := by
  match second with
  | .nil _ => exact .nil source
  | .cons member head tail =>
    let original := Classical.choose (first.origin member)
    have originalMember := (Classical.choose_spec (first.origin member)).1
    let entry := Classical.choice (Classical.choose_spec (first.origin member)).2
    exact .cons originalMember (entry.comp head) (first.comp tail)
termination_by (2 * n + 1, sizeOf second)
decreasing_by all_goals simp_wf; omega
end

mutual
noncomputable def AtomAdapter.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {a b : Atom n} (adapter : AtomAdapter env U registry Γ a b) :
    AtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, adapter with
  | _, _, _, .refl atom => exact .refl (atom.rename ρ)
  | _ + 1, _, _, .fn keys result =>
    exact .fn (keys.future henv W) (result.future henv W)
  | _ + 1, _, _, .pad adapter => exact .pad (adapter.future henv W)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileAdapter.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {source target : Profile n} (adapter : ProfileAdapter env U registry Γ source target) :
    ProfileAdapter env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.future henv W) (tail.future henv W)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def KeyProgram.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {old new : Key n} (program : KeyProgram env U registry Γ old new) :
    KeyProgram env U registry Δ (old.rename ρ) (new.rename ρ) := by
  match program with
  | .refl key => exact .refl (key.rename ρ)
  | .input seed arguments => exact .input (seed.future henv W) (arguments.future henv W)
  | .reanchor admitted => exact .reanchor (Admitted.future henv W admitted)
  | .domainRekey path typed formed bridge =>
    have formed' := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at formed'
    exact .domainRekey (path.weak' henv W.weakening)
      (Profile.rename_hasType_iff.mpr typed) formed' (TypeRelated.future henv W bridge)
  | .comp left right => exact .comp (left.future henv W) (right.future henv W)
termination_by (3 * n + 2, sizeOf program)
decreasing_by all_goals simp_wf; omega
end

noncomputable def AdapterSeed.mixed (henv : env.Ordered)
    (W : MixedInsertion env U Γ Δ ρ)
    (seed : AdapterSeed env U registry Γ key input) :
    AdapterSeed env U registry Δ (key.rename ρ) (input.rename ρ) := by
  match seed with
  | .same => exact .same
  | .supplied admitted => exact .supplied (W.admitted henv admitted)
  | .view previous change => exact .view (previous.mixed henv W) (change.mixed henv W)
termination_by sizeOf seed
decreasing_by simp_wf; omega

mutual
noncomputable def AtomAdapter.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {a b : Atom n} (adapter : AtomAdapter env U registry Γ a b) :
    AtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, adapter with
  | _, _, _, .refl atom => exact .refl (atom.rename ρ)
  | _ + 1, _, _, .fn keys result =>
    exact .fn (keys.mixed henv W) (result.mixed henv W)
  | _ + 1, _, _, .pad adapter => exact .pad (adapter.mixed henv W)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileAdapter.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {source target : Profile n} (adapter : ProfileAdapter env U registry Γ source target) :
    ProfileAdapter env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.mixed henv W) (tail.mixed henv W)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def KeyProgram.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {old new : Key n} (program : KeyProgram env U registry Γ old new) :
    KeyProgram env U registry Δ (old.rename ρ) (new.rename ρ) := by
  match program with
  | .refl key => exact .refl (key.rename ρ)
  | .input seed arguments => exact .input (seed.mixed henv W) (arguments.mixed henv W)
  | .reanchor admitted => exact .reanchor (W.admitted henv admitted)
  | .domainRekey path typed formed bridge =>
    have formed' := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at formed'
    exact .domainRekey (W.path henv path)
      (Profile.rename_hasType_iff.mpr typed) formed' (W.code henv bridge)
  | .comp left right => exact .comp (left.mixed henv W) (right.mixed henv W)
termination_by (3 * n + 2, sizeOf program)
decreasing_by all_goals simp_wf; omega
end

noncomputable def KeyProgram.arguments {old new : Key n}
    (program : KeyProgram env U registry Γ old new) :
    ProfileAdapter env U registry Γ new.input old.input := by
  match program with
  | .refl key => exact .refl key.input
  | .input _ arguments => exact arguments
  | .reanchor _ => exact .refl _
  | .domainRekey _ _ _ _ => exact .refl _
  | .comp left right => exact right.arguments.comp left.arguments
termination_by sizeOf program
decreasing_by all_goals simp_wf; omega

theorem AtomAdapter.fn_inv {atom : Atom (n + 1)} {key : Key n} {output : Atom n}
    (adapter : AtomAdapter env U registry Γ atom (.fn key output)) :
    ∃ sourceKey sourceOutput,
      atom = .fn sourceKey sourceOutput ∧
      Nonempty (KeyProgram env U registry Γ sourceKey key) ∧
      Nonempty (AtomAdapter env U registry Γ sourceOutput output) := by
  cases adapter with
  | refl => exact ⟨key, output, rfl, ⟨.refl _⟩, ⟨.refl _⟩⟩
  | fn keys result => exact ⟨_, _, rfl, ⟨keys⟩, ⟨result⟩⟩

noncomputable def AtomAdapter.extendInput {key : Key n} {output : Atom n} {input : Profile n}
    (seed : AdapterSeed env U registry Γ key input)
    (included : List.Subset key.input input) :
    AtomAdapter env U registry Γ (n := n + 1)
      (.fn key output) (.fn (inputKey key input) output) :=
  .fn (.input seed (.select included)) (.refl output)

def AtomAdapter.fnOutput (key : Key n) {output output' : Atom n}
    (result : AtomAdapter env U registry Γ output output') :
    AtomAdapter env U registry Γ (n := n + 1) (.fn key output) (.fn key output') :=
  .fn (.refl key) result

end Lean4Lean.AnchoredSemantics
