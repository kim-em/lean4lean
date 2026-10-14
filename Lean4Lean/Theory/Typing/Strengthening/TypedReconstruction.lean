import Lean4Lean.Theory.Typing.Strengthening.ConstructorParameterChange

/-! # Typed reconstruction with explicit constructor parameter changes

Finite compatible eta expansion is extended by its derived parameter-change
root. Soundness and the existing syntactic head-observation model survive.
Mixed computational postponement and terminal confluence remain separate tasks.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- The derived root is visible to the old head model as structure eta followed
by ordinary projection computation. It needs no checked prefix reduction. -/
theorem ConstructorParameterChange.observation (H : ConstructorParameterChange Γ a b) :
    ConstructorObservation.EtaCompute D a b := by
  cases H with
  | @intro family info levels' Γ levels params fields T params' hi hx hp hp' hf hz ha hb =>
    have HF : List.Forall₂ (ProjectionCompute D)
        ((List.range info.numFields).map (fun i => .proj family i
          (mkApps (.const info.ctorName levels) (params ++ fields)))) fields := by
      apply List.forall₂_of_getElem (by simp [hf])
      intro i hiP hiF
      simp only [List.getElem_map, List.getElem_range]
      exact .projIota hi (by simp [hp, hf]) (by
        rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem hiF)
    have spine {f f' xs ys} (R : ProjectionCompute D f f')
        (H : List.Forall₂ (ProjectionCompute D) xs ys) :
        ProjectionCompute D (mkApps f xs) (mkApps f' ys) := by
      induction H generalizing f f' with
      | nil => exact R
      | cons H _ ih => exact ih (.app R H)
    exact (ConstructorObservation.EtaCompute.structEta hi hx hz hp').trans
      (.compute (spine (.base .refl) ((List.Forall₂.rfl (fun _ _ => ProjectionCompute.base .refl)).append' HF)))

/-- Compatible finite reconstruction, retaining actual eta expansions and
explicit field-preserving constructor parameter changes. It contains no generic
conversion rule, and no computational completeness is assumed. -/
inductive TypedReconstruction : List VExpr → VExpr → VExpr → Prop where
  | refl : TypedReconstruction Γ e e
  | eta : TypedEtaExpansion Γ a b → TypedReconstruction Γ a b
  | parameters : ConstructorParameterChange Γ a b → TypedReconstruction Γ a b
  | trans : TypedReconstruction Γ a b → TypedReconstruction Γ b c → TypedReconstruction Γ a c
  | app : TypedReconstruction Γ f f' → TypedReconstruction Γ a a' →
      TypedReconstruction Γ (.app f a) (.app f' a')
  | lam : TypedReconstruction Γ A A' → TypedReconstruction (A :: Γ) b b' →
      TypedReconstruction Γ (.lam A b) (.lam A' b')
  | forallE : TypedReconstruction Γ A A' → TypedReconstruction (A :: Γ) B B' →
      TypedReconstruction Γ (.forallE A B) (.forallE A' B')
  | proj : TypedReconstruction Γ a b → TypedReconstruction Γ (.proj s i a) (.proj s i b)

/-- Reconstruction consists of actual full reductions from every typed source. -/
theorem TypedReconstruction.full (R : TypedReconstruction Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T) : FullReduction Γ a b := by
  induction R generalizing T with
  | refl => exact .rfl
  | eta R => exact R.full
  | parameters R => exact R.full hΓ
  | trans R _ ih1 ih2 =>
    have HR := ih1 hΓ ht
    exact HR.trans (ih2 hΓ (HR.hasType hΓ ht))
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact FullReduction.app (ih1 hΓ hf) (ih2 hΓ ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact FullReduction.lam (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact FullReduction.forallE (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact FullReduction.proj (ih hΓ hm.hasType.2)

/-- Soundness preserves independent source typings, including converted types. -/
theorem TypedReconstruction.simAt (R : TypedReconstruction Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ a b :=
  fun _ ht => (R.full hΓ ht).defeq hΓ ht

/-- Finite reconstruction retains the original head-observation interpretation.
Only source typing is used to recover contexts below binders. -/
theorem TypedReconstruction.observation (R : TypedReconstruction Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T) :
    ConstructorObservation.EtaCompute D a b := by
  induction R generalizing T with
  | refl => exact .compute (.base .refl)
  | eta R => exact R.observation hΓ ht
  | parameters R => exact R.observation
  | trans R _ ih1 ih2 => exact (ih1 hΓ ht).trans (ih2 hΓ (R.simAt hΓ _ ht).hasType.2)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ih1 hΓ hf) (ih2 hΓ ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2)

/-- Reconstruction cannot create Pi syntax, including through parameter changes. -/
theorem TypedReconstruction.forallE_source (R : TypedReconstruction Γ e (.forallE A B)) :
    ∃ A' B', e = .forallE A' B' := by
  generalize hout : VExpr.forallE A B = target at R
  induction R generalizing A B with
  | refl => exact ⟨_, _, hout.symm⟩
  | eta R => subst hout; exact R.forallE_source
  | parameters H =>
    cases H
    have hh := congrArg getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | trans _ _ ih1 ih2 =>
    obtain ⟨A', B', he⟩ := ih2 hout
    exact ih1 he.symm
  | forallE => exact ⟨_, _, rfl⟩
  | app | lam | proj => cases hout

end Lean4Lean.VEnv.Strengthening.PureObservation
