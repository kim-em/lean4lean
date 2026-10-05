import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction

/-! Actual source Pi provenance classifies every typed finite value demand.
Padding is normalized explicitly; no raw-type uniqueness is used. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def NormalFunction : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, atom => ∃ key output, AdapterNormal.atom atom = AtomData.fn key output

theorem PiProfileOrigins.value_shape
    {value : Profile n} {atom : Atom n}
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile n))
    (typed : value.HasType profile)
    (member : atom ∈ value.atoms) : NormalFunction atom := by
  induction n with
  | zero =>
    obtain ⟨cover, hm, _⟩ := typed atom member
    exact (origins cover hm).elim
  | succ n ih =>
    obtain ⟨cover, hm, ht⟩ := typed.2.2 atom member
    have origin := origins cover hm
    cases cover with
    | sort | fn | family | ctor | record => exact origin.elim
    | pi protoDomain protoBody domain rows =>
      cases atom with
      | sort | pi | pad | family | ctor | record => contradiction
      | fn key output => exact ⟨AdapterNormal.key key, AdapterNormal.atom output, rfl⟩
    | pad cover =>
      cases atom with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad atom =>
        have smaller : PiProfileOrigins env U registry target locals σ available A B
            (Profile.singleton cover) := by
          intro a hm
          cases List.mem_singleton.mp hm
          exact origin
        have shape := ih smaller ht (List.mem_singleton_self _)
        cases n with
        | zero => exact shape.elim
        | succ n =>
          obtain ⟨key, output, he⟩ := shape
          refine ⟨AdapterNormal.shiftKey key, AdapterNormal.shiftAtom output, ?_⟩
          rw [AdapterNormal.atom_pad, he]
          rfl

end Lean4Lean.AnchoredSource.Adapted
