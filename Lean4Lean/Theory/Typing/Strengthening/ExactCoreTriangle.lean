import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Exact complete-development triangle for core computation

Core beta/pattern parallel reduction has an exact triangle through its existing
complete-development relation. Typing transports dependent body contexts and
pattern checks; no normal-comparison remainder is needed.
-/
namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- Every core parallel step reaches the same complete development by one
further core parallel step, with literal equality of endpoints. -/
theorem ParRed.triangle_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : Γ ⊢ e : A) (H : ParRed Γ e e') (H2 : CParRed Γ e o) : ParRed Γ e' o := by
  induction e using VExpr.brecOn generalizing Γ A e' o with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  induction H2 generalizing A e' with
  | bvar =>
    cases H with
    | bvar => exact .rfl
    | extra h1 h2 => cases h2
  | sort =>
    cases H with
    | sort => exact .rfl
    | extra h1 h2 => cases h2
  | const hn =>
    cases H with
    | const => exact .rfl
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := H1.app_inv henv hΓ
    cases H with
    | app r1 r2 => exact .app (ih1 hΓ l1 r1 e_ih.1.2) (ih2 hΓ l2 r2 e_ih.2.2)
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
    | beta => cases hn (.inl ⟨_, _, _, rfl⟩)
  | proj hn _ ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := H1.proj_inv henv hΓ
    cases H with
    | proj rMajor => exact .proj (ihMajor hΓ hmajor.hasType.2 rMajor e_ih.2)
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.lam_inv henv hΓ
    cases H with
    | lam r1 r2 =>
      have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, l1⟩
      have p1 := ih1 hΓ l1 r1 e_ih.1.2
      have p2 := ih2 hΓ' l2 r2 e_ih.2.2
      exact .lam p1 (p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType hΓ' l2))
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.forallE_inv henv
    cases H with
    | forallE r1 r2 =>
      have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, l1⟩
      have p1 := ih1 hΓ l1 r1 e_ih.1.2
      have p2 := ih2 hΓ' l2 r2 e_ih.2.2
      exact .forallE p1 (p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType hΓ' l2))
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := H1.app_inv henv hΓ
    have ⟨⟨_, lA⟩, _, le⟩ := lf.lam_inv henv hΓ
    have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lA le)).forallE_inv henv hΓ
    have la' := hw.defeq la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
      ⟨ha, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    rcases H.app_lam_cases with ⟨_, _, rf, ra, rfl⟩ | ⟨_, _, re, ra, rfl⟩
    · have p3 := ha hΓ la ra l2
      cases rf with
      | lam rA re =>
        have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, lA⟩
        have p2 := he hΓ' le re l1
        exact .beta (p2.defeqDFC hΓ (.succ .zero (rA.defeq hΓ lA)) (re.hasType hΓ' le)) p3
      | extra h1 h2 => cases h2
    · have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, lA⟩
      have p2 := he hΓ' le re l1
      have p3 := ha hΓ la ra l2
      exact .instN p3 (ra.hasType hΓ la') .zero p2
  | @extra p r e m1 m2 Γ m2' l1 l2 l3 l4 ih =>
    have split :
      (∃ m3 : p.Path → VExpr, p.Matches e' m1 m3 ∧
        (∀ a, ParRed Γ (m2 a) (m3 a)) ∧ (∀ a, ParRed Γ (m3 a) (m2' a))) ∨
      (∃ p₁ e₁' e₁ m1₁ m2₁, Subpattern p₁ p ∧ (p₁ = p → e₁ = e ∧ e₁' = e' ∧ m1₁ ≍ m1 ∧ m2₁ ≍ m2) ∧
        p₁.Matches e₁ m1₁ m2₁ ∧ ∃ p' r m1 m2 m2',
        Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ (∀ a, ParRed Γ (m2 a) (m2' a)) ∧ e₁' = r.1.apply m1 m2') := by
      have hnative := Params.constHeaded l1
      clear l1 l3 l4 r
      induction H generalizing p m1 A with
      | const =>
        cases id l2; exact .inl ⟨_, l2, nofun, nofun⟩
      | @app Γ f f' a a' hf ha ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        cases l2 with
        | var lf =>
          match ih1 lf (ih <| some ·) hΓ Hf e_ih.1.2 hnative with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.varL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.varL .refl)
          | .inl ⟨_, f1, f2, f3⟩ =>
            have a3 := ih none hΓ Ha ha e_ih.2.2
            exact .inl ⟨_, .var f1, (·.casesOn ha f2), (·.casesOn a3 f3)⟩
        | app lf la =>
          match ih1 lf (ih <| .inl ·) hΓ Hf e_ih.1.2 hnative.1 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.appL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.appL .refl)
          | .inl ⟨_, f1, f2, f3⟩ =>
            match ih2 la (ih <| .inr ·) hΓ Ha e_ih.2.2 hnative.2 with
            | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
              refine .inr ⟨_, _, _, _, _, h1.appR, ?_, h3⟩
              rintro rfl; cases h1.antisymm (.appR .refl)
            | .inl ⟨_, a1, a2, a3⟩ =>
              exact .inl ⟨_, .app f1 a1, (·.casesOn f2 a2), (·.casesOn f3 a3)⟩
      | beta _ _ => cases l2 with | var h | app h => cases h
      | @extra _ _ _ _ _ _ _ r1 r2 _ r4 =>
        exact .inr ⟨_, _, _, _, _, .refl, fun _ => ⟨rfl, rfl, .rfl, .rfl⟩,
          l2, _, _, _, _, _, r1, r2, r4, rfl⟩
      | _ => cases l2
    match split with
    | .inl ⟨m3, hm, h2, h3⟩ =>
      refine .extra l1 hm (l3.map fun _ _ ⟨_, h1⟩ => ?_) h3
      refine ⟨_, .trans
        (.symm <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.1)
        (.trans h1 <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.2)⟩
    | .inr ⟨_, _, _, _, _, h1, h2, l2', _, _, _, _, m3, r1, r2, r4, ee⟩ =>
      obtain ⟨_, -, -, hr, -⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2'⟩⟩
      obtain ⟨rfl, rfl, ⟨⟩⟩ := pat_uniq l1 r1 h1 hr
      obtain ⟨rfl, rfl, ⟨⟩, ⟨⟩⟩ := h2 rfl; subst ee
      obtain ⟨rfl, rfl⟩ := l2'.uniq r2
      suffices ∀ a, ParRed Γ (m3 a) (m2' a) from .apply_pat _ this
      clear H r l1 l2 l3 l4 split h1 h2 r1 r2 hr
      induction l2' generalizing A with
      | const => exact nofun
      | app _ _ ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have h1 := ih1 (ih <| .inl ·) _ Hf e_ih1 (r4 <| .inl ·)
        have h2 := ih2 (ih <| .inr ·) _ Ha e_ih2 (r4 <| .inr ·)
        exact (·.casesOn h1 h2)
      | var _ ih1 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have h1 := ih1 (ih <| some ·) _ Hf e_ih1 (r4 <| some ·)
        have h2 := ih none hΓ Ha (r4 none) e_ih2
        exact (·.casesOn h2 h1)

/-- Core parallel computation has an exact typed diamond. -/
theorem ParRed.diamond_exact (hΓ : OnCtx Γ (env.IsType univs))
    (ha : Γ ⊢ a : A) (H1 : ParRed Γ a b) (H2 : ParRed Γ a c) :
    ∃ d, ParRed Γ b d ∧ ParRed Γ c d := by
  obtain ⟨d, HD⟩ := CParRed.exists hΓ ha
  exact ⟨d, H1.triangle_exact hΓ ha HD, H2.triangle_exact hΓ ha HD⟩

end Lean4Lean.VEnv
