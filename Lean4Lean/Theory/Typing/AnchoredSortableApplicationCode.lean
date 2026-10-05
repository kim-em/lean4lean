import Lean4Lean.Theory.Typing.AnchoredApplication
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

/-! A sortable function result is code directly from its actual application
row. No separately chosen codomain support or literal assigned Pi shape is
needed to extract that code capability.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.applicationCode
    {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sortable : (Profile.singleton output).HasType (.sort relevant))
    (function : Related env U registry target f g functionType
      (Profile.fn key output) functionSupport)
    (admitted : Admitted env U registry target key x y) :
    TypeRelated env U registry target (.app f x) (.app g y) (.singleton output) := by
  have base := function (.fn key output) (List.mem_singleton_self _) target .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  rcases base with empty | ⟨Ω, τ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn (key.rename τ) (output.rename τ))
      (by simp only [Profile.rename_singleton, Atom.rename_fn]; exact List.mem_singleton_self _)
    obtain ⟨_, oldA, oldB, oldDomain, rows, oldResult, _, _, _, display, applyRow⟩ := behavior
    have full := MixedInsertion.comp (.proof insertion) (display.leftExposure.insertion henv)
    have args := full.admitted henv admitted
    have row := applyRow display.context .refl (.refl (full.targetWF henv formed))
      (x.lift' (τ.comp display.map)) (y.lift' (τ.comp display.map)) (by
        simpa only [Lift.comp, Key.rename_comp, Admitted] using args)
    simp only [Lift.comp, lift'_depth_zero (l := Lift.refl.cons) rfl] at row
    have pair := Related.trans henv hscoped row.2.2 row.2.1
    have sorted := (Profile.rename_hasType_iff (ρ := τ.comp display.map)).mpr sortable
    rw [Profile.rename_sort] at sorted
    have code := pair.code_of_sortable henv hscoped (full.targetWF henv formed) (by
      simpa only [← Atom.rename_comp, Profile.rename_singleton] using sorted)
    apply full.codeBack henv hscoped
    simpa only [lift', ← lift'_comp, ← Atom.rename_comp, Profile.rename_singleton] using code

end Lean4Lean.AnchoredSemantics
