import Lean4Lean.Theory.Typing.AnchoredLiteralPi
import Lean4Lean.Theory.Typing.AnchoredTransitivity

/-! Applying a genuine function observation at its literal dependent type.
The result uses the supplied actual codomain capability; private display
supports are retagged before their proof insertions are absorbed. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem exposureInsertion {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

theorem Related.apply
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {f g A B x y : VExpr} {key : Key n} {output : Atom n}
    {functionType : Profile (n + 1)} {result : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (typed : (Profile.singleton output).HasType result)
    (code : TypeRelated env U registry Γ (B.inst x) (B.inst x) result)
    (function : Related env U registry Γ f g (.forallE A B)
      (.fn key output) functionType)
    (admitted : Admitted env U registry Γ key x y) :
    Related env U registry Γ (.app f x) (.app g y) (B.inst x)
      (.singleton output) result := by
  have base := function (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at base
  rcases base with empty | ⟨Ω, τ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn (key.rename τ) (output.rename τ))
      (by simp only [Profile.rename_singleton, Atom.rename_fn]; exact List.mem_singleton_self _)
    obtain ⟨_, oldA, oldB, oldDomain, rows, oldResult, _, _, _, display, applyRow⟩ := behavior
    have full := MixedInsertion.comp (.proof insertion) (exposureInsertion henv display.leftExposure)
    have args := full.admitted henv admitted
    have row := applyRow display.context .refl (.refl (full.targetWF henv hΓ))
      (x.lift' (τ.comp display.map)) (y.lift' (τ.comp display.map)) (by
        simpa only [Lift.comp, Key.rename_comp, Admitted] using args)
    simp only [Lift.comp, lift'_depth_zero (l := Lift.refl.cons) rfl] at row
    have body := display.leftExposure.literalPi_components |>.2
    have body_eq : display.leftBody.inst (x.lift' (τ.comp display.map)) =
        (B.inst x).lift' (τ.comp display.map) := by
      rw [body, ← lift'_comp, lift'_inst_hi]
      rfl
    have pair := Related.trans henv hscoped row.2.2 row.2.1
    rw [body_eq] at pair
    have typed' := (Profile.rename_hasType_iff (ρ := τ.comp display.map)).mpr typed
    have code' := full.code henv code
    have changed := Related.retag henv typed' code' (by
      simpa only [← lift'_comp, ← Atom.rename_comp, Profile.rename_singleton] using pair)
    apply full.termBack henv
    simpa only [lift', Profile.rename_singleton] using changed

end Lean4Lean.AnchoredSemantics
