import Lean4Lean.Theory.Typing.Strengthening.DomainNormal

/-! # Composition of recursive domain comparisons

Context conversion and substitution retain the recorded domain certificates. This
file checks that symmetry and transitivity do so too; it makes no completeness claim.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- Symmetry retains the comparison index, including at dependent binders. -/
theorem DomainNormal.symm (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DomainNormal n Γ a b) : DomainNormal n Γ b a := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | projDF h H ih =>
    have ht := ((DomainNormal.projDF h H).defeq hΓ).of_l henv hΓ h
    exact .projDF ht.hasType.2 (ih hΓ)
  | lamDF hA HA _ ihA ihb =>
    have haa := (HA.defeq hΓ).of_l henv hΓ hA
    exact .lamDF haa.hasType.2 (ihA hΓ)
      ((ihb ⟨hΓ, _, hA⟩).defeqDFC (.succ .zero haa))
  | forallEDF hA HA hB HB ihA ihB =>
    have haa := (HA.defeq hΓ).of_l henv hΓ hA
    have hbb := (HB.defeq (by exact ⟨hΓ, _, hA⟩)).of_l henv (by exact ⟨hΓ, _, hA⟩) hB
    exact .forallEDF haa.hasType.2 (ihA hΓ) (hbb.hasType.2.defeqDFC henv (.succ .zero haa))
      ((ihB ⟨hΓ, _, hA⟩).defeqDFC (.succ .zero haa))
  | proofIrrel hP ha hb => exact .proofIrrel hP hb ha

/-- Transitivity preserves recursive domain certificates. The middle lambda's
body comparison is moved to the first domain using an already certified equality. -/
theorem DomainNormal.trans (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    DomainNormal n₁ Γ a b → DomainNormal n₂ Γ b c → ∃ n, DomainNormal n Γ a c
  | .sortDF l1 _ l3, .sortDF _ r2 r3 => ⟨_, .sortDF l1 r2 (l3.trans r3)⟩
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 _ r5 =>
    ⟨_, .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)⟩
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 => by
    obtain ⟨_, hf⟩ := l5.trans hΓ r5
    obtain ⟨_, ha⟩ := l6.trans hΓ r6
    exact ⟨_, .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4) hf ha⟩
  | .projDF l1 l2, .projDF _ r2 => by
    obtain ⟨_, h⟩ := l2.trans hΓ r2
    exact ⟨_, .projDF l1 h⟩
  | .lamDF l1 l2 l3, .lamDF _ r2 r3 => by
    obtain ⟨_, hA⟩ := l2.trans hΓ r2
    have haa := (l2.defeq hΓ).of_l henv hΓ l1
    obtain ⟨_, hb⟩ := l3.trans (by exact ⟨hΓ, _, l1⟩) (r3.defeqDFC (.succ .zero haa.symm))
    exact ⟨_, .lamDF l1 hA hb⟩
  | .forallEDF l1 l2 l3 l4, .forallEDF _ r2 _ r4 => by
    obtain ⟨_, hA⟩ := l2.trans hΓ r2
    have haa := (l2.defeq hΓ).of_l henv hΓ l1
    obtain ⟨_, hb⟩ := l4.trans (by exact ⟨hΓ, _, l1⟩) (r4.defeqDFC (.succ .zero haa.symm))
    exact ⟨_, .forallEDF l1 hA l3 hb⟩
  | .refl _, H2 => ⟨_, H2⟩
  | .proofIrrel l1 l2 l3, H2 =>
    ⟨_, .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)⟩
  | H1, .refl _ => ⟨_, H1⟩
  | H1, .proofIrrel h1 h2 h3 =>
    ⟨_, .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3⟩
termination_by n₁ + n₂

/-- Binder insertion preserves every comparison certificate and its index. -/
theorem DomainNormal.weakN (W : Ctx.LiftN k j Γ Γ') (H : DomainNormal n Γ a b) :
    DomainNormal n Γ' (a.liftN k j) (b.liftN k j) := by
  induction H generalizing j Γ' with
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W)
      (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.weakN henv W) (ih W)
  | lamDF hA _ _ ihA ihb => exact .lamDF (hA.weakN henv W) (ihA W) (ihb W.succ)
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.weakN henv W) (ihA W) (hB.weakN henv W.succ) (ihB W.succ)
  | proofIrrel hP ha hb => exact .proofIrrel (hP.weakN henv W) (ha.weakN henv W) (hb.weakN henv W)

/-- Substituting related arguments into one typed term yields a recursive domain
comparison, in the context instantiated with the left argument. Its index may grow. -/
theorem DomainNormal.instN_r (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e : A) :
    ∃ m, DomainNormal m Γ (e.inst e₀ k) (e.inst e₀' k) := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := H.bvar_inv henv hΓ₁
    clear H hΓ₁
    induction W generalizing i ty with
    | zero =>
      cases h with simp
      | zero => exact ⟨_, H'⟩
      | succ h => exact ⟨_, .refl (.bvar h)⟩
    | succ _ ih =>
      cases h with simp
      | zero => exact ⟨_, .refl (.bvar .zero)⟩
      | succ h =>
        obtain ⟨_, hh⟩ := ih _ _ h
        exact ⟨_, hh.weakN .one⟩
  | sort => exact ⟨_, .refl (.sort (H.sort_inv henv))⟩
  | const =>
    let ⟨_, h1, h2, h3⟩ := H.const_inv henv hΓ₁
    exact ⟨_, .refl (.const h1 h2 h3)⟩
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := H.app_inv henv hΓ₁
    obtain ⟨_, Hf⟩ := ih1 hΓ₁ W h1
    obtain ⟨_, Ha⟩ := ih2 hΓ₁ W h2
    have hf := h1.instN henv W h₀
    have ha := h2.instN henv W h₀
    let ⟨_, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact ⟨_, .appDF hf (.defeqU_l henv hΓ (Hf.defeq hΓ) hf) ha
      (.defeqU_l henv hΓ (Ha.defeq hΓ) ha) Hf Ha⟩
  | proj typeName index major ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := H.proj_inv henv hΓ₁
    obtain ⟨_, HM⟩ := ihMajor hΓ₁ W hmajor.hasType.2
    exact ⟨_, .projDF (H.instN henv W h₀) HM⟩
  | lam A body ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ₁
    obtain ⟨_, HA⟩ := ih1 hΓ₁ W h1
    obtain ⟨_, HB⟩ := ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2
    exact ⟨_, .lamDF (h1.instN henv W h₀) HA HB⟩
  | forallE A B ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    obtain ⟨_, HA⟩ := ih1 hΓ₁ W h1
    obtain ⟨_, HB⟩ := ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2
    exact ⟨_, .forallEDF (h1.instN henv W h₀) HA (h2.instN henv W.succ h₀) HB⟩

/-- Heterogeneous substitution preserves recursive domain comparisons, including
all newly created beta-redexes. No decreasing-index claim is made. -/
theorem DomainNormal.instN_lr (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : DomainNormal m Γ₁ e1 e2) :
    ∃ j, DomainNormal j Γ (e1.inst e₀ k) (e2.inst e₀' k) := by
  obtain ⟨_, hh⟩ := H.defeq hΓ₁
  obtain ⟨_, hr⟩ := DomainNormal.instN_r hΓ₁ h₀ H' W hh.hasType.2
  exact (H.instN W h₀).trans (W.wf henv h₀ hΓ₁).2 hr

end Lean4Lean.VEnv.Strengthening
