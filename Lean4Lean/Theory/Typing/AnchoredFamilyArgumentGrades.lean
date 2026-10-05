import Lean4Lean.Theory.Typing.AnchoredFamilyCodeWitness
import Lean4Lean.Theory.Typing.AnchoredGradedAdapters

/-! A finite heterogeneous family request is equivalent to one list of keys
at a common lower grade. This lets family atoms keep the existing primitive
recursion on grade, while declaration rows retain their original exact grades. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource
set_option backward.isDefEq.respectTransparency false

private theorem lower_raised {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    lowerProfile n bound (raiseProfile N bound profile) = profile := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simp only [raiseProfile_self, lowerProfile_self]
    · have low : n ≤ N := by omega
      rw [lowerProfile_step low, raiseProfile_step low, Profile.down_pad]
      exact ih low

def raiseDataRequest (N : Nat) (bound : n ≤ N) (request : DataRequest (Profile n)) :
    DataRequest (Profile N) :=
  ⟨raiseKey N bound request.toKeyData, raiseProfile N bound request.support⟩

def FamilyKey.uniform (N : Nat) : (keys : List FamilyKey) →
    (∀ key ∈ keys, key.rank ≤ N) → List (DataRequest (Profile N))
  | [], _ => []
  | key :: keys, bounded =>
    raiseDataRequest N (bounded key List.mem_cons_self) key.request ::
      uniform N keys (fun key member => bounded key (List.mem_cons_of_mem _ member))

/-- Raise only the input/support grades; the literal domain and anchor stay
fixed. This operation does not require a new source observation. -/
theorem Admitted.raiseFamily {key : Key n} (henv : env.Ordered) (bound : n ≤ N)
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (raiseKey N bound key) x y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, last⟩ := admitted
  exact ⟨anchor, pair, raiseProfile N bound support,
    Profile.HasType.raise bound typed, Profile.HasType.raise_sort bound formed,
    TypeRelated.raise henv bound code, Related.raise henv bound first,
    Related.raise henv bound last⟩

/-- The support selected at the common grade may be arbitrary. Lowering the
actual raised request recovers its original admission and a concrete support. -/
theorem Admitted.lowerFamily {key : Key n} (henv : env.Ordered) (bound : n ≤ N)
    (hΓ : OnCtx Γ (env.IsType U))
    (admitted : Admitted env U registry Γ (raiseKey N bound key) x y) :
    Admitted env U registry Γ key x y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, last⟩ := admitted
  exact ⟨anchor, pair, lowerProfile n bound support,
    Profile.HasType.lower bound typed, Profile.HasType.lower_sort bound formed,
    TypeRelated.lower henv bound code, Related.lower henv bound hΓ first,
    Related.lower henv bound hΓ last⟩

theorem RankedData.RequestAdmission.raiseFamily {request : DataRequest (Profile n)}
    (henv : env.Ordered) (bound : n ≤ N)
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) Γ request x y) :
    RankedData.RequestAdmission env U (relations env U registry N) Γ
      (raiseDataRequest N bound request) x y := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admitted
  exact ⟨anchor, pair, Profile.HasType.raise bound typed,
    Profile.HasType.raise_sort bound formed, TypeRelated.raise henv bound code,
    Related.raise henv bound first, Related.raise henv bound last⟩

theorem RankedData.RequestAdmission.lowerFamily {request : DataRequest (Profile n)}
    (henv : env.Ordered) (bound : n ≤ N) (hΓ : OnCtx Γ (env.IsType U))
    (admitted : RankedData.RequestAdmission env U (relations env U registry N) Γ
      (raiseDataRequest N bound request) x y) :
    RankedData.RequestAdmission env U (relations env U registry n) Γ request x y := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admitted
  have typed' := Profile.HasType.lower bound typed
  have formed' := Profile.HasType.lower_sort bound formed
  have code' := TypeRelated.lower henv bound code
  have first' := Related.lower henv bound hΓ first
  have last' := Related.lower henv bound hΓ last
  simp only [raiseDataRequest, lower_raised] at typed' formed' code' first' last'
  exact ⟨anchor, pair, typed', formed', code', first', last'⟩

theorem FamilyArguments.uniform
    (henv : env.Ordered) (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    (arguments : FamilyArguments env U registry Γ keys xs ys) :
    RankedData.Arguments env U (relations env U registry N) Γ (FamilyKey.uniform N keys bounded) xs ys := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (RankedData.RequestAdmission.raiseFamily henv (bounded _ List.mem_cons_self) head)
      (ih (fun key member => bounded key (List.mem_cons_of_mem _ member)))

theorem FamilyArguments.of_uniform
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    (arguments : RankedData.Arguments env U (relations env U registry N) Γ (FamilyKey.uniform N keys bounded) xs ys) :
    FamilyArguments env U registry Γ keys xs ys := by
  induction keys generalizing xs ys with
  | nil => cases arguments; exact .nil
  | cons key keys ih =>
    cases arguments with
    | cons head tail =>
      exact .cons (RankedData.RequestAdmission.lowerFamily henv (bounded key List.mem_cons_self) hΓ head)
        (ih (fun key member => bounded key (List.mem_cons_of_mem _ member)) tail)

/-- One common lower grade represents exactly the same finite demand. Thus
the heterogeneous declaration traversal introduces no non-well-founded query. -/
theorem FamilyArguments.uniform_iff
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    FamilyArguments env U registry Γ keys xs ys ↔
      RankedData.Arguments env U (relations env U registry N) Γ (FamilyKey.uniform N keys bounded) xs ys :=
  ⟨FamilyArguments.uniform henv N bounded, FamilyArguments.of_uniform henv hΓ N bounded⟩

end Lean4Lean.AnchoredSemantics
