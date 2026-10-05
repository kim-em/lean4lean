import Lean4Lean.Theory.Typing.AnchoredAdapters
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionInterpretation

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
mutual
inductive GeneralAtomAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Atom n → Atom n → Type where
  | code {a b : Atom n} {flag next : Bool}
      (action : AnchoredSource.Adapted.SortableCodeAction env U registry Γ flag (.singleton a) next (.singleton b))
      (formed : (Profile.singleton a).HasType (.sort flag)) :
      GeneralAtomAdapter env U registry Γ a b
  | refl (atom : Atom n) : GeneralAtomAdapter env U registry Γ atom atom
  | fn {key newKey : Key n} {output output' : Atom n}
      (keys : GeneralKeyProgram env U registry Γ key newKey)
      (result : GeneralAtomAdapter env U registry Γ output output') :
      GeneralAtomAdapter env U registry Γ (n := n + 1) (.fn key output) (.fn newKey output')
  | pad {atom atom' : Atom n} (adapter : GeneralAtomAdapter env U registry Γ atom atom') :
      GeneralAtomAdapter env U registry Γ (n := n + 1) (.pad atom) (.pad atom')

/-- Every output atom names an actual input origin. Unused input atoms may be
discarded and the same input origin may be used more than once. -/
inductive GeneralProfileAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Profile n → Profile n → Type where
  | nil (source : Profile n) : GeneralProfileAdapter env U registry Γ source []
  | cons {source target : Profile n} {atom output : Atom n}
      (member : atom ∈ source.atoms)
      (head : GeneralAtomAdapter env U registry Γ atom output)
      (tail : GeneralProfileAdapter env U registry Γ source target) :
      GeneralProfileAdapter env U registry Γ source (output :: target)

/-- Key programs operate on admissions at the rank below a function atom.
Their intermediate guards are concrete; they request no intermediate
function type capability. -/
inductive GeneralKeyProgram (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Key n → Key n → Type where
  | refl (key : Key n) : GeneralKeyProgram env U registry Γ key key
  | input {key : Key n} {input : Profile n}
      (seed : AdapterSeed env U registry Γ key input)
      (arguments : GeneralProfileAdapter env U registry Γ input key.input) :
      GeneralKeyProgram env U registry Γ key (inputKey key input)
  | reanchor {key : Key n} {anchor : VExpr}
      (admitted : Admitted env U registry Γ key anchor anchor) :
      GeneralKeyProgram env U registry Γ key (reanchorKey key anchor)
  | domainRekey {key : Key n} {newDomain : VExpr} {guard : Profile n}
      (path : TypeConversion env U Γ key.domain newDomain)
      (typed : key.input.HasType guard) (formed : guard.HasType (.sort true))
      (bridge : TypeRelated env U registry Γ key.domain newDomain guard) :
      GeneralKeyProgram env U registry Γ key (domainKey key newDomain)
  | comp {first middle last : Key n}
      (left : GeneralKeyProgram env U registry Γ first middle)
      (right : GeneralKeyProgram env U registry Γ middle last) :
      GeneralKeyProgram env U registry Γ first last
end

theorem GeneralProfileAdapter.origin
    (adapter : GeneralProfileAdapter env U registry Γ source target)
    (member : atom ∈ target.atoms) :
    ∃ original, original ∈ source.atoms ∧
      Nonempty (GeneralAtomAdapter env U registry Γ original atom) := by
  match adapter with
  | .nil _ => cases member
  | .cons sourceMember head tail =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, sourceMember, ⟨head⟩⟩
    · exact tail.origin member
termination_by sizeOf adapter
decreasing_by simp_wf; omega

def GeneralProfileAdapter.refl (source : Profile n) :
    GeneralProfileAdapter env U registry Γ source source := by
  let rec go (target : Profile n) (included : List.Subset target source) :
      GeneralProfileAdapter env U registry Γ source target :=
    match target with
    | [] => .nil source
    | atom :: tail => .cons (included List.mem_cons_self) (.refl atom)
        (go tail (fun _ hm => included (List.mem_cons_of_mem _ hm)))
  exact go source (fun _ h => h)

noncomputable def GeneralProfileAdapter.select (included : List.Subset target source) :
    GeneralProfileAdapter env U registry Γ source target := by
  induction target with
  | nil => exact .nil source
  | cons atom tail ih =>
    exact .cons (included List.mem_cons_self) (.refl atom)
      (ih (fun _ hm => included (List.mem_cons_of_mem _ hm)))

mutual
noncomputable def GeneralAtomAdapter.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b) :
    GeneralAtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, adapter with
  | _, _, _, .refl atom => exact .refl (atom.rename ρ)
  | _, _, _, .code action formed =>
    apply GeneralAtomAdapter.code (by simpa only [Profile.rename_singleton] using action.future henv W)
    simpa only [Profile.rename_singleton, Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
  | _ + 1, _, _, .fn keys result =>
    exact .fn (keys.future henv W) (result.future henv W)
  | _ + 1, _, _, .pad adapter => exact .pad (adapter.future henv W)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralProfileAdapter.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {source target : Profile n} (adapter : GeneralProfileAdapter env U registry Γ source target) :
    GeneralProfileAdapter env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.future henv W) (tail.future henv W)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralKeyProgram.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {old new : Key n} (program : GeneralKeyProgram env U registry Γ old new) :
    GeneralKeyProgram env U registry Δ (old.rename ρ) (new.rename ρ) := by
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

mutual
noncomputable def GeneralAtomAdapter.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b) :
    GeneralAtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, adapter with
  | _, _, _, .refl atom => exact .refl (atom.rename ρ)
  | _, _, _, .code action formed =>
    apply GeneralAtomAdapter.code (by simpa only [Profile.rename_singleton] using action.mixed henv W)
    simpa only [Profile.rename_singleton, Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
  | _ + 1, _, _, .fn keys result =>
    exact .fn (keys.mixed henv W) (result.mixed henv W)
  | _ + 1, _, _, .pad adapter => exact .pad (adapter.mixed henv W)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralProfileAdapter.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {source target : Profile n} (adapter : GeneralProfileAdapter env U registry Γ source target) :
    GeneralProfileAdapter env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.mixed henv W) (tail.mixed henv W)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def GeneralKeyProgram.mixed (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {old new : Key n} (program : GeneralKeyProgram env U registry Γ old new) :
    GeneralKeyProgram env U registry Δ (old.rename ρ) (new.rename ρ) := by
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


end Lean4Lean.AnchoredSemantics
