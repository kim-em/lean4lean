import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterInterpretation

/-! A concrete argument-side promotion excluded by legacy key programs.
The old function key stays unchanged; its actual seed supplies the final
support used to pull the argument relation backward. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

noncomputable def GeneralAtomAdapter.sortPromotion {n : Nat} {flag relevant : Bool}
    (formed : (Profile.singleton (n := n + 1) (.sort flag)).HasType (.sort relevant)) :
    GeneralAtomAdapter env U registry Γ (n := n + 2)
      (.pad (.sort flag)) (.sort flag) := by
  apply GeneralAtomAdapter.code
    (show SortableCodeAction env U registry Γ relevant
      (Profile.singleton (n := n + 2) (.pad (.sort flag))) relevant
      (Profile.singleton (n := n + 2) (.sort flag)) from by
        simpa only [Profile.sort, Profile.pad, Profile.singleton, Profile.mk, List.map_cons, List.map_nil] using
          (SortableCodeAction.comp
            (SortableCodeAction.unpad (profile := Profile.sort (n := n + 1) flag))
            SortableCodeAction.sortPad))
  exact formed.pad_sort

noncomputable def GeneralProfileAdapter.sortPromotion {n : Nat} {flag relevant : Bool}
    (formed : (Profile.singleton (n := n + 1) (.sort flag)).HasType (.sort relevant)) :
    GeneralProfileAdapter env U registry Γ (n := n + 2)
      (.singleton (.pad (.sort flag))) (.singleton (.sort flag)) :=
  .cons (List.mem_singleton_self _) (.sortPromotion formed) (.nil _)

noncomputable def GeneralKeyProgram.sortPromotion {n : Nat} {flag relevant : Bool}
    {key : Key (n + 2)}
    (oldInput : key.input = .singleton (.sort flag))
    (formed : (Profile.singleton (n := n + 1) (.sort flag)).HasType (.sort relevant))
    (seed : AdapterSeed env U registry Γ key (.singleton (.pad (.sort flag)))) :
    GeneralKeyProgram env U registry Γ key
      (inputKey key (.singleton (.pad (.sort flag)))) := by
  apply GeneralKeyProgram.input seed
  rw [oldInput]
  exact .sortPromotion formed

/-- The source of the final argument support is the old function's seed,
not an inverse transformation of a certificate at the new input. -/
theorem GeneralKeyProgram.sortPromotion_pull {n : Nat} {flag relevant : Bool}
    {key : Key (n + 2)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (oldInput : key.input = .singleton (.sort flag))
    (formed : (Profile.singleton (n := n + 1) (.sort flag)).HasType (.sort relevant))
    (nextSeed : AdapterSeed env U registry Γ key (.singleton (.pad (.sort flag))))
    (oldSeed : Admitted env U registry Γ key key.anchor key.anchor)
    (argument : Admitted env U registry Γ
      (inputKey key (.singleton (.pad (.sort flag)))) x y) :
    Admitted env U registry Γ key x y :=
  (GeneralKeyProgram.sortPromotion oldInput formed nextSeed).pull henv hscoped hΓ oldSeed argument

end Lean4Lean.AnchoredSemantics
