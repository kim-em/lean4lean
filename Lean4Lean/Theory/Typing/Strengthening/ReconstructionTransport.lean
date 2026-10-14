import Lean4Lean.Theory.Typing.Strengthening.TypedReconstruction
import Lean4Lean.Theory.Typing.Strengthening.FreshBetaReflection

/-! # Context transport and fresh-argument reconstruction

Reconstruction preserves actual root witnesses under weakening and context
conversion. Exact fresh-argument beta reflection lets reconstruction stay below
a lambda while beta computation moves into the original function.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Weakening preserves the common typing and literally shared fields. -/
theorem ConstructorParameterChange.weakN (R : ConstructorParameterChange Γ a b)
    (W : Ctx.LiftN n k Γ Γ') :
    ConstructorParameterChange Γ' (a.liftN n k) (b.liftN n k) := by
  cases R with
  | intro hi hx hp hp' hf hz ha hb =>
    have ha' := ha.weakN henv W
    have hb' := hb.weakN henv W
    simp only [liftN_mkApps, liftN, List.map_append] at ha' hb' ⊢
    exact .intro hi hx (by simpa using hp) (by simpa using hp')
      (by simpa using hf) hz ha' hb'

/-- Ambient context conversion preserves both root typings. -/
theorem ConstructorParameterChange.defeqDFC (R : ConstructorParameterChange Γ₁ a b)
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) : ConstructorParameterChange Γ₂ a b := by
  cases R with
  | intro hi hx hp hp' hf hz ha hb =>
    exact .intro hi hx hp hp' hf hz (ha.defeqDFC henv W) (hb.defeqDFC henv W)

/-- Weakening preserves both typings of every root expansion. -/
theorem TypedReconstruction.weakN (R : TypedReconstruction Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    TypedReconstruction Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing Γ' k with
  | refl => exact .refl
  | eta R => exact .eta (R.weakN W)
  | parameters R => exact .parameters (R.weakN W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Ambient context conversion retains the actual expansion witnesses. -/
theorem TypedReconstruction.defeqDFC (R : TypedReconstruction Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : TypedReconstruction Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | refl => exact .refl
  | eta R => exact .eta (R.defeqDFC hΓ W ht)
  | parameters R => exact .parameters (R.defeqDFC W)
  | trans R1 _ ih1 ih2 => exact .trans (ih1 W ht) (ih2 W (R1.simAt (W.isType' hΓ) _ ht).hasType.2)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hA) (ih2 (.succ W hA) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (.succ W hA) hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)

/-- A beta path from a fresh application followed by reconstruction lifts back
to beta and reconstruction of the function. The reconstructed body is compared
under the original Pi domain; no reconstruction descent is assumed. -/
theorem fresh_beta_reconstruction (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RB : BetaRed (.app f.lift (.bvar 0)) body0)
    (RE : TypedReconstruction (A :: Γ) body0 body1)
    (HN : NormalEq (A :: Γ) body1 body2) :
    ∃ f0 f1, BetaRed f f0 ∧ TypedReconstruction Γ f0 f1 ∧
      NormalEq Γ f1 (.lam A body2) := by
  obtain ⟨f0, RF, hout⟩ := beta_fresh_application RB
  have hf0 := (RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf).hasType.2
  obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  rcases hout with rfl | ⟨D, rfl⟩
  · exact ⟨_, _, RF, (TypedReconstruction.eta (.funEta hf0)).trans (.lam .refl RE), .lamDF hA hA HN⟩
  · obtain ⟨⟨_, hD⟩, _, hb⟩ := hf0.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := ((hD.lam hb).uniqU henv hΓ hf0).forallE_inv henv hΓ
    have ht0 := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓA _
      (HasType.app (hf.weak henv) (.bvar .zero))).hasType.2
    have RE' := RE.defeqDFC hΓ (.succ .zero hDA.symm) ht0
    exact ⟨_, _, RF, .lam .refl RE', .lamDF hDA.symm hDA.hasType.2 HN⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
