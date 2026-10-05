import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaTransfer
import Lean4Lean.Theory.Typing.AnchoredGradedAdapters

/-! Raising the declared lambda input preserves its exact source leaves. -/
namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem raiseProfile_subset {small large : Profile n} (bound : n ≤ N)
    (included : ∀ atom ∈ small.atoms, atom ∈ large.atoms) :
    ∀ atom ∈ (raiseProfile N bound small).atoms,
      atom ∈ (raiseProfile N bound large).atoms := by
  induction N with
  | zero =>
    have eq : n = 0 := by omega
    subst n
    exact included
  | succ N ih =>
    by_cases eq : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using included
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, raiseProfile_step hn]
      intro atom member
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
      exact List.mem_map_of_mem (ih hn a ha)

theorem Need.atGrade_raise (need : Need) (bound : n ≤ N) (low : need.rank ≤ n) :
    need.atGrade N = raiseProfile N bound (need.atGrade n) := by
  simp only [Need.atGrade, dif_pos low, dif_pos (Nat.le_trans low bound), raiseProfile_trans]

theorem BinderPack.raise {input : Profile n}
    (pack : BinderPack n input footprint outside) (bound : n ≤ N) :
    BinderPack N (raiseProfile N bound input) footprint outside := by
  induction pack with
  | nil => simpa only [raiseProfile_empty] using BinderPack.nil (n := N)
  | «local» need low rest ih =>
    simpa only [raiseProfile_union, ← Need.atGrade_raise need bound low] using
      BinderPack.local need (Nat.le_trans low bound) ih
  | external i need rest ih => exact .external i need ih

theorem Admitted.raise {key : Key n} (henv : env.Ordered) (bound : n ≤ N)
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (raiseKey N bound key) x y := by
  induction N with
  | zero =>
    have eq : n = 0 := by omega
    subst n
    simpa only [raiseKey_self] using admitted
  | succ N ih =>
    by_cases eq : n = N + 1
    · subst n
      simpa only [raiseKey_self] using admitted
    · have hn : n ≤ N := by omega
      rw [raiseKey_step hn]
      exact Admitted.pad henv (ih hn)

theorem LambdaGuard.raise {key : Key n} (henv : env.Ordered) (bound : n ≤ N)
    (guard : LambdaGuard env U registry Γ σ annotation key support) :
    LambdaGuard env U registry Γ σ annotation (raiseKey N bound key)
      (raiseProfile N bound support) :=
  ⟨Profile.HasType.raise bound guard.inputTyped, Profile.HasType.raise_sort bound guard.formed, guard.path,
    TypeRelated.raise henv bound guard.domains, Admitted.raise henv bound guard.anchor⟩

end Lean4Lean.AnchoredSource
