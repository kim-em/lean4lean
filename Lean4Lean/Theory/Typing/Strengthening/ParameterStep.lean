import Lean4Lean.Theory.Typing.Strengthening.ReconstructionTransport

/-! # Single compatible constructor parameter changes

The source domain indexes body steps. This exposes one derived root at a time
for transport through normal comparison, without assuming mixed postponement.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Exactly one constructor parameter change at any compatible position. -/
inductive ParameterStep : List VExpr → VExpr → VExpr → Prop where
  | root : ConstructorParameterChange Γ a b → ParameterStep Γ a b
  | appL : ParameterStep Γ f f' → ParameterStep Γ (.app f a) (.app f' a)
  | appR : ParameterStep Γ a a' → ParameterStep Γ (.app f a) (.app f a')
  | lamL : ParameterStep Γ A A' → ParameterStep Γ (.lam A b) (.lam A' b)
  | lamR : ParameterStep (A :: Γ) b b' → ParameterStep Γ (.lam A b) (.lam A b')
  | forallL : ParameterStep Γ A A' → ParameterStep Γ (.forallE A B) (.forallE A' B)
  | forallR : ParameterStep (A :: Γ) B B' → ParameterStep Γ (.forallE A B) (.forallE A B')
  | proj : ParameterStep Γ m m' → ParameterStep Γ (.proj s i m) (.proj s i m')

/-- A single compatible step is a finite reconstruction. -/
theorem ParameterStep.toReconstruction (R : ParameterStep Γ a b) : TypedReconstruction Γ a b := by
  induction R with
  | root R => exact .parameters R
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

/-- Weakening retains each actual parameter-change typing. -/
theorem ParameterStep.weakN (R : ParameterStep Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    ParameterStep Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing Γ' k with
  | root R => exact .root (R.weakN W)
  | appL _ ih => exact .appL (ih W)
  | appR _ ih => exact .appR (ih W)
  | lamL _ ih => exact .lamL (ih W)
  | lamR _ ih => exact .lamR (ih W.succ)
  | forallL _ ih => exact .forallL (ih W)
  | forallR _ ih => exact .forallR (ih W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Typed conversion of the ambient context preserves a single parameter step. -/
theorem ParameterStep.defeqDFC (R : ParameterStep Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : ParameterStep Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | root R => exact .root (R.defeqDFC W)
  | appL _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .appL (ih W hf)
  | appR _ ih =>
    obtain ⟨_, _, _, ha⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .appR (ih W ha)
  | lamL _ ih =>
    obtain ⟨⟨_, hA⟩, _, _⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lamL (ih W hA)
  | lamR _ ih =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lamR (ih (.succ W hA) hb)
  | forallL _ ih =>
    obtain ⟨⟨_, hA⟩, _, _⟩ := ht.forallE_inv henv
    exact .forallL (ih W hA)
  | forallR _ ih =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.forallE_inv henv
    exact .forallR (ih (.succ W hA) hb)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)

end Lean4Lean.VEnv.Strengthening.PureObservation
