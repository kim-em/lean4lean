import Lean4Lean.Theory.Typing.Strengthening.RecursiveLoopBodies

/-! # Comparing bodies at distinct recursive domains

A normal comparison between two hereditary loop bodies at distinct recursive
domains cannot use either recursive role. This includes extensional comparison:
the fresh applications are tracked before removing their binders syntactically.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Every computational node avoids the recursive domain type. Annotations are
not traversed; all their conversion behavior remains available. -/
inductive NoRecursive (c : Name) : List VExpr → VExpr → Prop where
  | bvar : ¬ env.HasType univs Γ (.bvar i) (domain c) → NoRecursive c Γ (.bvar i)
  | app : ¬ env.HasType univs Γ (.app f a) (domain c) →
      NoRecursive c Γ f → NoRecursive c Γ a → NoRecursive c Γ (.app f a)
  | lam : ¬ env.HasType univs Γ (.lam A b) (domain c) →
      NoRecursive c (A :: Γ) b → NoRecursive c Γ (.lam A b)

theorem NoRecursive.not_recursive (H : NoRecursive c Γ e) :
    ¬ env.HasType univs Γ e (domain c) := by cases H <;> assumption

theorem NoRecursive.defeqDFC (H : NoRecursive c Γ₁ e)
    (He : LoopBody c Γ₁ e) (hΓ : OnCtx Γ₁ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) : NoRecursive c Γ₂ e := by
  induction H generalizing Γ₂ with
  | bvar hn => exact .bvar fun ht => hn (ht.defeqDFC henv (W.symm henv))
  | app hn _ _ ihf iha =>
    cases He with
    | app _ Hf Ha =>
      exact .app (fun ht => hn (ht.defeqDFC henv (W.symm henv))) (ihf Hf hΓ W) (iha Ha hΓ W)
  | lam hn _ ih =>
    cases He with
    | lam ht Hb =>
      obtain ⟨_, ht⟩ := ht
      obtain ⟨⟨_, hA⟩, _, _⟩ := ht.lam_inv henv hΓ
      exact .lam (fun ht => hn (ht.defeqDFC henv (W.symm henv)))
        (ih Hb ⟨hΓ, _, hA⟩ (.succ W hA))

theorem NoRecursive.of_liftN (H : NoRecursive c Γ' (e.liftN n k))
    (W : Ctx.LiftN n k Γ Γ') : NoRecursive c Γ e := by
  induction e generalizing Γ Γ' k with
  | bvar =>
    exact .bvar fun ht => H.not_recursive (by simpa [domain, liftN] using ht.weakN henv W)
  | app f a ihf iha =>
    cases H with
    | app hn Hf Ha =>
      exact .app (fun ht => hn (by simpa [domain, liftN] using ht.weakN henv W)) (ihf Hf W) (iha Ha W)
  | lam A b _ ihb =>
    cases H with
    | lam hn Hb =>
      exact .lam (fun ht => hn (by simpa [domain, liftN] using ht.weakN henv W)) (ihb Hb W.succ)
  | sort | const | proj | forallE => cases H

section
variable
  (hδc : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
  (hsep : ∀ {Δ}, OnCtx Δ (env.IsType univs) → ¬ env.IsDefEqU univs Δ (domain c) (domain d))

include hδc hsep

/-- A term at the other domain's roles cannot also have the recursive type. -/
theorem HasLoopRole.cross_not_recursive (H : HasLoopRole d Γ e)
    (hΓ : OnCtx Γ (env.IsType univs)) : ¬ env.HasType univs Γ e (domain c) := by
  intro hc
  obtain ⟨r, hr⟩ := H
  have ht := hc.uniqU henv hΓ hr
  cases r with
  | recursive => exact hsep hΓ ht
  | function => exact domain_not_result hδc hΓ ht
  | proposition => exact domain_not_prop hδc hΓ ht

theorem LoopBody.cross_same (Hc : LoopBody c Γ e) (Hd : LoopBody d Γ e)
    (hΓ : OnCtx Γ (env.IsType univs)) : NoRecursive c Γ e := by
  induction Hc with
  | bvar => exact .bvar (Hd.role.cross_not_recursive hδc hsep hΓ)
  | app _ _ _ ihf iha =>
    have hn := Hd.role.cross_not_recursive hδc hsep hΓ
    cases Hd with
    | app _ Hf Ha => exact .app hn (ihf Hf hΓ) (iha Ha hΓ)
  | lam ht _ ih =>
    have hn := Hd.role.cross_not_recursive hδc hsep hΓ
    obtain ⟨_, he⟩ := ht
    obtain ⟨hA, _, _⟩ := he.lam_inv henv hΓ
    cases Hd with
    | lam _ Hb => exact .lam hn (ih Hb ⟨hΓ, hA⟩)

theorem NormalEqN.cross_not_recursive (H : NormalEqN mode n Γ e out)
    (Hd : LoopBody d Γ out) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ env.HasType univs Γ e (domain c) := by
  intro ht
  exact Hd.role.cross_not_recursive hδc hsep hΓ
    ((H.defeq hΓ).of_l henv hΓ ht).hasType.2

/-- A normal comparison of bodies using distinct recursive domains has no
recursive-typed computational node on the left. Both eta directions and
extensionality are included, without a strengthening premise. -/
theorem NormalEqN.cross_noRecursive
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδd : ∀ Δ, env.IsDefEq univs Δ (domain d) (domainValue d) (.sort (.succ .zero)))
    (H : NormalEqN mode n Γ e out) (Hc : LoopBody c Γ e) (Hd : LoopBody d Γ out)
    (hΓ : OnCtx Γ (env.IsType univs)) : NoRecursive c Γ e := by
  induction H with
  | refl => exact Hc.cross_same hδc hsep Hd hΓ
  | sortDF | constDF | projDF | forallEDF => cases Hc
  | appDF hf hf' ha ha' Hf Ha ihf iha =>
    have hn := NormalEqN.cross_not_recursive hδc hsep (NormalEqN.appDF hf hf' ha ha' Hf Ha) Hd hΓ
    cases Hc with
    | app _ Hcf Hca =>
      cases Hd with
      | app _ Hdf Hda => exact .app hn (ihf Hcf Hdf hΓ) (iha Hca Hda hΓ)
  | lamDF hA1 hA2 Hb ih =>
    have hn := NormalEqN.cross_not_recursive hδc hsep (NormalEqN.lamDF hA1 hA2 Hb) Hd hΓ
    cases Hc with
    | lam _ Hcb =>
      cases Hd with
      | lam _ Hdb =>
        have Hcb' := Hcb.defeqDFC ⟨hΓ, _, hA1.hasType.2⟩ (.succ .zero hA1.symm)
        have Hdb' := Hdb.defeqDFC ⟨hΓ, _, hA2.hasType.2⟩ (.succ .zero hA2.symm)
        have hb := ih Hcb' Hdb' ⟨hΓ, _, hA1.hasType.1⟩
        exact .lam hn (hb.defeqDFC Hcb' ⟨hΓ, _, hA1.hasType.1⟩ (.succ .zero hA1))
  | etaL hf Hb ih =>
    have hn := NormalEqN.cross_not_recursive hδc hsep (NormalEqN.etaL hf Hb) Hd hΓ
    have Hde := Hd.eta hδd hΓ hf
    cases Hc with
    | lam ht Hcb =>
      obtain ⟨_, he⟩ := ht
      obtain ⟨hA, _, _⟩ := he.lam_inv henv hΓ
      cases Hde with
      | lam _ Hdb => exact .lam hn (ih Hcb Hdb ⟨hΓ, hA⟩)
  | etaR hf Hb ih =>
    have Hce := Hc.eta hδc hΓ hf
    cases Hd with
    | lam ht Hdb =>
      obtain ⟨_, he⟩ := ht
      obtain ⟨hA, _, _⟩ := he.lam_inv henv hΓ
      cases Hce with
      | lam _ Hcb =>
        have hb := ih Hcb Hdb ⟨hΓ, hA⟩
        cases hb with
        | app _ Hf _ => exact Hf.of_liftN .one
  | etaBoth hf hf' Hb ih =>
    have Hce := Hc.eta hδc hΓ hf
    have Hde := Hd.eta hδd hΓ hf'
    have hA := (hf.isType henv hΓ).forallE_inv henv |>.1
    cases Hce with
    | lam _ Hcb =>
      cases Hde with
      | lam _ Hdb =>
        have hb := ih Hcb Hdb ⟨hΓ, hA⟩
        cases hb with
        | app _ Hf _ => exact Hf.of_liftN .one
  | proofIrrel hP he _ =>
    obtain ⟨r, ht⟩ := Hc.role
    exact (LoopRole.not_proof hc hΓ ht ⟨_, he, hP⟩).elim

end

end Lean4Lean.VEnv.Strengthening.GuardedEta
