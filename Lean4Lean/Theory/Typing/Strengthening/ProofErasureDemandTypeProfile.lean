import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlTyping

/-! # Dependent type profiles for finite computational demands

An ignored domain imposes no shape condition. Observed results are universes
or arrows whose domains and codomains carry profiles in their actual dependent
contexts. All evidence is ordinary typing and equality, never native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Only demanded portions of a type have a prescribed shape. -/
inductive Profile where
  | ignored
  | sort
  | arrow (domain result : Profile)

/-- An observable profile ends in a universe. An ignored profile supplies
no finite observation, although it may occur as a function's domain. -/
inductive Profile.Visible : Profile → Prop where
  | sort : Visible .sort
  | arrow : Visible B → Visible (.arrow A B)

variable [Params]

/-- A profile follows actual dependent Pi representatives. An ignored type
must still be well formed; no closedness or nondependency condition is imposed. -/
def Fits (Γ : List VExpr) (T : VExpr) : Profile → Prop
  | .ignored => env.IsType univs Γ T
  | .sort => env.IsType univs Γ T ∧ ∃ u, env.IsDefEqU univs Γ T (.sort u)
  | .arrow p q => env.IsType univs Γ T ∧ ∃ A B,
      env.IsDefEqU univs Γ T (.forallE A B) ∧ Fits Γ A p ∧ Fits (A :: Γ) B q

/-- Every profile retains the well-formedness of its represented type. -/
theorem Fits.isType (H : Fits Γ T p) : env.IsType univs Γ T := by
  cases p with
  | ignored => exact H
  | sort | arrow => exact H.1

/-- Ordinary type equality changes the represented expression while retaining
the profile and its dependent representative telescope. -/
theorem Fits.convert (hΓ : OnCtx Γ (env.IsType univs))
    (H : Fits Γ T p) (E : env.IsDefEqU univs Γ T T') : Fits Γ T' p := by
  have HT := H.isType.defeqU_l henv hΓ E
  cases p with
  | ignored => exact HT
  | sort =>
    obtain ⟨_, u, HU⟩ := H
    exact ⟨HT, u, E.symm.trans henv hΓ HU⟩
  | arrow p q =>
    obtain ⟨_, A, B, HE, HA, HB⟩ := H
    exact ⟨HT, A, B, E.symm.trans henv hΓ HE, HA, HB⟩

/-- Every ordinary typed substitution preserves a profile. Its arrow branch
uses the actual substituted domain, so dependent parameters need no native
image certificate and no closed control-domain approximation. -/
theorem Fits.subst (H : Fits Γ T p)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    Fits Γ₀ (T.subst σ) p := by
  induction p generalizing Γ Γ₀ T σ with
  | ignored => exact IsType.subst henv.orderedStrong W H hΓ₀
  | sort =>
    obtain ⟨HT, u, E⟩ := H
    exact ⟨HT.subst henv.orderedStrong W hΓ₀, u, E.subst henv.orderedStrong W hΓ₀⟩
  | arrow p q ihp ihq =>
    obtain ⟨HT, A, B, E, HA, HB⟩ := H
    obtain ⟨u, hA⟩ := HA.isType
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    exact ⟨HT.subst henv.orderedStrong W hΓ₀, A.subst σ, B.subst σ.lift,
      E.subst henv.orderedStrong W hΓ₀, ihp HA hΓ₀ W, ihq HB hΓA (W.lift henv.ordered hA)⟩

/-- Context conversion transports the dependent profile without changing its
expression or requiring native identity images. -/
theorem Fits.context (H : Fits Γ T p) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HC : IsDefEqCtx env univs [] Γ Γ') : Fits Γ' T p := by
  have W : Ctx.SubstEq env univs Γ' VExpr.Subst.id VExpr.Subst.id Γ :=
    substEq_source_convert hΓ' (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓ')
  simpa only [VExpr.subst_id] using H.subst hΓ' W

/-- A literal Pi may be read in its own original domain and codomain rather
than the alternative representatives stored in the profile. -/
theorem Fits.forallE_inv (hΓ : OnCtx Γ (env.IsType univs))
    (H : Fits Γ (.forallE A B) (.arrow p q)) : Fits Γ A p ∧ Fits (A :: Γ) B q := by
  obtain ⟨HT, A', B', E, HA, HB⟩ := H
  obtain ⟨u, hPi⟩ := HT
  obtain ⟨⟨v, hA⟩, w, hB⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
  obtain ⟨⟨_, EA⟩, _, EB⟩ := E.forallE_inv henv hΓ
  have HC : IsDefEqCtx env univs [] (A' :: Γ) (A :: Γ) := .succ (.refl hΓ) EA.symm
  exact ⟨HA.convert hΓ EA.toU.symm, (HB.context hΓA HC).convert hΓA EB.toU.symm⟩

/-- Observable profiles have a strictly positive universe, including arrows
whose ignored domain is a proposition or a dependent data family. -/
theorem Fits.positive (hΓ : OnCtx Γ (env.IsType univs))
    (H : Fits Γ T p) (HV : p.Visible) :
    ∃ u, env.HasType univs Γ T (.sort u) ∧ u.IsNeverZero := by
  induction HV generalizing Γ T with
  | sort =>
    obtain ⟨⟨v, hT⟩, u, E⟩ := H
    have hS := hT.defeqU_l henv hΓ E
    have hu := hS.sort_inv henv.ordered
    refine ⟨.succ u, (HasType.sort hu).defeqU_l henv hΓ E.symm, ?_⟩
    intro ls
    simp [VLevel.eval]
  | arrow HV ih =>
    obtain ⟨_, A, B, E, HA, HB⟩ := H
    obtain ⟨u, hA⟩ := HA.isType
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨v, hB, hv⟩ := ih hΓA HB
    refine ⟨.imax u v, (HasType.forallE hA hB).defeqU_l henv hΓ E.symm, ?_⟩
    intro ls
    simp [VLevel.eval, Lean.Nat.imax, hv ls, Nat.max_eq_zero_iff]

/-- A value observed at a visible profile cannot erase as a proof. -/
theorem Fits.not_isProof (hΓ : OnCtx Γ (env.IsType univs))
    (H : Fits Γ T p) (HV : p.Visible) (ht : env.HasType univs Γ e T) : ¬ IsProof Γ e := by
  rintro ⟨P, heP, hP⟩
  obtain ⟨u, hT, hu⟩ := H.positive hΓ HV
  have hT0 := hP.defeqU_l henv hΓ (ht.uniqU henv hΓ heP).symm
  have E := (hT.uniqU henv hΓ hT0).sort_inv henv hΓ
  exact hu [] (congrFun E [])

end Lean4Lean.VEnv.Strengthening.DemandProfile
