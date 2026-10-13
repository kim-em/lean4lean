import Lean4Lean.Theory.Typing.Strengthening.CastComputation

/-! # Typed replay across non-syntactic cast endpoints

A cast and its payload with a common typing are definitionally equal under
canonical Eq. If both are types, their shared endpoint universe aligns their
sort levels without strengthening or ambient equality. This provides typed
replay beyond the syntactic K rule when a payload sort typing can be recovered.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Common source/payload typing recovers endpoint conversion by uniqueness,
so the cast contracts even when its endpoint syntax is different. -/
theorem cast_eq_of_common_typing (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.HasType U Γ (typeCast u X Y p x) T)
    (hx : env.HasType U Γ x T) :
    env.IsDefEq U Γ (typeCast u X Y p x) x T := by
  obtain ⟨hu, hX, hY, hp, hxX⟩ := typeCast_typings henv heq hΓ ⟨_, hc⟩
  have hcY := HasType.typeCast henv.ordered heq hu hX hY hp hxX
  have hXT := hxX.uniqU henv hΓ hx
  have hYT := hcY.uniqU henv hΓ hc
  have hXY := (hXT.trans henv hΓ hYT.symm).of_l henv hΓ hX
  exact IsDefEq.trans_l henv hΓ hc (IsDefEq.typeCast_refl henv heq hu hΓ hXY hp hxX)

/-- When a cast and its payload are both types, uniqueness at the common
endpoint universe aligns their sort levels. No ambient equality is needed. -/
theorem cast_type_eq (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.HasType U Γ (typeCast u X Y p x) (.sort v))
    (hx : env.IsType U Γ x) :
    env.IsDefEq U Γ (typeCast u X Y p x) x (.sort v) := by
  obtain ⟨w, hxw⟩ := hx
  obtain ⟨hu, hX, hY, hp, hxX⟩ := typeCast_typings henv heq hΓ ⟨_, hc⟩
  have hcY := HasType.typeCast henv.ordered heq hu hX hY hp hxX
  have hXw := (hxX.uniqU henv hΓ hxw).of_l henv hΓ hX
  have hYv := (hcY.uniqU henv hΓ hc).of_l henv hΓ hY
  have hw := hxw.sort_r henv hΓ
  have hv := hc.sort_r henv hΓ
  have huw := (hXw.hasType.2.uniqU henv hΓ (HasType.sort hw)).sort_inv henv hΓ
  have huv := (hYv.hasType.2.uniqU henv hΓ (HasType.sort hv)).sort_inv henv hΓ
  have hwv := VLevel.succ_congr_iff.1 (huw.symm.trans huv)
  exact cast_eq_of_common_typing henv heq hΓ hc ((IsDefEq.sortDF hw hv hwv).defeqDF hxw)

/-- A computational Pi exposure of the payload supplies its missing sort typing
below. Universe alignment then replays the cast and follows that computation,
without any ambient equality or syntactic endpoint match. This is a local cast
bridge; it does not eliminate eta from arbitrary payload traces. -/
theorem cast_pi_exposure_below [Params]
    (heq : Params.env.HasCanonicalEq)
    (hs : PureObservation.Definitions.Sound D Params.env Params.univs)
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (hc : Params.env.HasType Params.univs Γ (typeCast u X Y p x) (.sort v))
    (R : CastCompute D (x.lift' ρ) (.forallE A B)) :
    ∃ A₀ B₀, Params.env.IsDefEq Params.univs Γ
      (typeCast u X Y p x) (.forallE A₀ B₀) (.sort v) := by
  have henv := Params.henv
  obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, hc⟩
  obtain ⟨out, R0, he⟩ := R.lift_inv
  obtain ⟨A₀, B₀, rfl, _, _⟩ := lift'_eq_forallE he.symm
  have hxpi := R0.simAt heq hs hΓ X hx
  obtain ⟨⟨a, hA⟩, ⟨b, hB⟩⟩ := HasType.forallE_inv henv.ordered hxpi.hasType.2
  have hxt : Params.env.IsType Params.univs Γ x :=
    IsType.defeqU_l henv hΓ ⟨_, hxpi.symm⟩ ⟨_, HasType.forallE hA hB⟩
  have hcx := cast_type_eq henv heq hΓ hc hxt
  exact ⟨A₀, B₀, hcx.trans_l henv hΓ hxpi⟩

end Lean4Lean.VEnv.Strengthening
