import Lean4Lean.Theory.Typing.Strengthening.DomainNormal
import Lean4Lean.Theory.Typing.FullReduction

/-! # Eta-aware descent with selective domain certificates

This adapts route A's `NormalDescent.lean`: application congruence admits lambda
functions when a `DomainNormal` certificate is available. Its eta/spine argument
and common-type lambda argument are otherwise retained. Recursive certificates are
required only at application functions, not at every lambda domain in the join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ[" n "] " e2:30 => NormalEqN true n Γ e1 e2

/-! ## Selective comparison -/

/-- Eta-aware normal comparison. Each application either has two non-lambda
functions or carries a recursive domain certificate for its function comparison.
All other constructors retain route A's strict relation. -/
inductive HybridNormal : Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → HybridNormal 0 Γ e e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → HybridNormal 0 Γ (.sort l₁) (.sort l₂)
  | constDF :
    Params.env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    HybridNormal 0 Γ (.const c ls) (.const c ls')
  | appDF :
    ((¬ IsLam f₁ ∧ ¬ IsLam f₂) ∨ ∃ j, DomainNormal j Γ f₁ f₂) →
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    HybridNormal n₁ Γ f₁ f₂ → HybridNormal n₂ Γ a₁ a₂ →
    HybridNormal (n₁ + n₂ + 1) Γ (.app f₁ a₁) (.app f₂ a₂)
  | projDF :
    Γ ⊢ .proj typeName index major : resultType →
    HybridNormal n Γ major major' →
    HybridNormal (n + 1) Γ (.proj typeName index major) (.proj typeName index major')
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    HybridNormal n (A::Γ) body₁ body₂ →
    HybridNormal (n + 1) Γ (.lam A₁ body₁) (.lam A₂ body₂)
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → HybridNormal n₁ Γ A₁ A₂ →
    A::Γ ⊢ B₁ : .sort v → HybridNormal n₂ (A::Γ) B₁ B₂ →
    HybridNormal (n₁ + n₂ + 1) Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | etaL :
    Γ ⊢ e' : .forallE A B →
    HybridNormal n (A::Γ) e (.app e'.lift (.bvar 0)) →
    HybridNormal (n + 2) Γ (.lam A e) e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    HybridNormal n (A::Γ) (.app e'.lift (.bvar 0)) e →
    HybridNormal (n + 2) Γ e' (.lam A e)
  | etaBoth :
    Γ ⊢ e : .forallE A B → Γ ⊢ e' : .forallE A B →
    HybridNormal n (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
    HybridNormal (n + 2) Γ e e'
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    HybridNormal 0 Γ h h'

local notation:65 Γ " ⊢ " e1 " ≡ₛ[" n "] " e2:30 => HybridNormal n Γ e1 e2

theorem HybridNormal.toNormalEqN (H : Γ ⊢ e1 ≡ₛ[n] e2) : Γ ⊢ e1 ≡ₚ[n] e2 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 ih1 ih2
  | projDF h _ ih => exact .projDF h ih
  | lamDF h1 h2 _ ih => exact .lamDF h1 h2 ih
  | forallEDF h1 _ h3 _ ih1 ih2 => exact .forallEDF h1 ih1 h3 ih2
  | etaL h _ ih => exact .etaL h ih
  | etaR h _ ih => exact .etaR h ih
  | etaBoth h1 h2 _ ih => exact .etaBoth h1 h2 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3

theorem HybridNormal.defeq (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : Γ ⊢ e1 ≡ₛ[n] e2) :
    Γ ⊢ e1 ≡ e2 := H.toNormalEqN.defeq hΓ

/-- Context conversion (as `NormalEqN.defeqDFC`). -/
theorem HybridNormal.defeqDFC (H₀ : OnCtx Γ₀ (Params.env.IsType univs))
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₛ[m] e2) : Γ₂ ⊢ e1 ≡ₛ[m] e2 := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF hside h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (hside.imp id (fun ⟨j, H⟩ => ⟨j, H.defeqDFC W⟩)) (.defeqDFC henv W h1) (.defeqDFC henv W h2)
      (.defeqDFC henv W h3) (.defeqDFC henv W h4) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (.defeqDFC henv W hproj) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (.defeqDFC henv W h1) (.defeqDFC henv W h2) (ih1 (W.succ h1.hasType.1))
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (.defeqDFC henv W h1) (ih1 W)
      (.defeqDFC henv (W.succ h1.hasType.1) h3) (ih2 (W.succ h1.hasType.1))
  | etaL h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    exact .etaL (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaR h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    exact .etaR (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaBoth h1 h1' _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    exact .etaBoth (.defeqDFC henv W h1) (.defeqDFC henv W h1') (ih (W.succ h2))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (.defeqDFC henv W h1) (.defeqDFC henv W h2) (.defeqDFC henv W h3)

/-! ## Fresh-variable spines: peeling an `etaBoth` body -/

/-- `e` applied to the variables `vs`, the head of the list outermost:
`varSpine e [v₁, …, vₘ] = e vₘ … v₁`. -/
def varSpine (e : VExpr) : List Nat → VExpr
  | [] => e
  | v :: vs => .app (varSpine e vs) (.bvar v)

omit [VEnv.Params] in
theorem varSpine_lift (e : VExpr) (ρ : Lift) (vs : List Nat) :
    (varSpine (e.lift' ρ) vs).lift = varSpine (e.lift' ρ.skip) (vs.map (· + 1)) := by
  induction vs with
  | nil => exact lift_lift'_skip e ρ
  | cons v vs ih => simp [varSpine, lift, liftN, ih, liftVar_base']

omit [VEnv.Params] in
theorem varSpine_inj {e e' : VExpr} : ∀ {vs : List Nat}, varSpine e vs = varSpine e' vs → e = e'
  | [], h => h
  | _ :: _, h => varSpine_inj (VExpr.app.inj h).1

/-- The function of a typed variable spine is typed. -/
theorem varSpine_fn_typed (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {vs : List Nat}, Γ ⊢ varSpine e vs : T → ∃ T', Γ ⊢ e : T'
  | [], h => ⟨_, h⟩
  | _ :: _, h => let ⟨_, _, hf, _⟩ := h.app_inv henv hΓ; varSpine_fn_typed hΓ hf

/-- If the eta body `e⇑ 0` is a proof then `e` is a proof: the codomain is a proposition, so the
`Π` type is one (`imax`). -/
theorem IsProof.of_etaBody (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : .forallE A B) (hp : IsProof (A :: Γ) (.app e.lift (.bvar 0))) :
    IsProof Γ e := by
  obtain ⟨⟨u, hA⟩, v, hB⟩ := (he.isType henv.ordered hΓ).forallE_inv henv.ordered
  have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨P, hbP, hP⟩ := hp
  have hb : A :: Γ ⊢ .app e.lift (.bvar 0) : B := by
    have := HasType.app (he.weak henv.ordered (B := A)) (.bvar .zero)
    simpa only [lift, liftN, inst_liftN_bvar] using this
  have hPv : A :: Γ ⊢ P : .sort v := ((hb.uniqU henv hΓA hbP).of_l henv hΓA hB).hasType.2
  have hv : v ≈ .zero := (hPv.uniqU henv hΓA hP).sort_inv henv hΓA
  have hPi : Γ ⊢ .forallE A B : .sort (.imax u v) := .forallE hA hB
  exact ⟨_, he, (IsDefEq.sortDF (hPi.sort_r henv.ordered hΓ) (by trivial)
    (VLevel.imax_eq_zero.2 hv)).defeq hPi⟩

omit [VEnv.Params] in
theorem Lift.skipN_succ' (ρ : Lift) (j : Nat) : ρ.skip.skipN j = ρ.skipN (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Lift.skipN, ih]

/-- **Peeling a spine comparison.** A hybrid normal equality between two variable spines of
lifts (same variables, not a proof) at index `n` yields a hybrid normal equality between the two
lifts, further lifted along the binders the peeling introduced, at an index at most `n`. The
`etaBoth` case extends the spine by a fresh variable and decreases the index; the `appDF` case
shortens it. -/
theorem HybridNormal.spine_inv : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {e e' : VExpr} {vs : List Nat},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ' (Params.env.IsType univs) →
    ¬ IsProof Γ' (varSpine (e.lift' ρ) vs) →
    Γ' ⊢ varSpine (e.lift' ρ) vs ≡ₛ[n] varSpine (e'.lift' ρ) vs →
    ∃ k, ∃ Δ : List VExpr, k ≤ n ∧ Ctx.Lift' (ρ.skipN Δ.length) Γ (Δ ++ Γ') ∧
      OnCtx (Δ ++ Γ') (Params.env.IsType univs) ∧
      Δ ++ Γ' ⊢ e.lift' (ρ.skipN Δ.length) ≡ₛ[k] e'.lift' (ρ.skipN Δ.length) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro ρ Γ Γ' e e' vs W hΓ' hn H
  cases vs with
  | nil => exact ⟨n, [], Nat.le_refl _, W, hΓ', H⟩
  | cons v vs =>
  simp only [varSpine] at H hn
  generalize hl : VExpr.app (varSpine (e.lift' ρ) vs) (.bvar v) = l at H
  generalize hr : VExpr.app (varSpine (e'.lift' ρ) vs) (.bvar v) = r at H
  cases H with
  | refl ht =>
    subst hl
    have hee : e.lift' ρ = e'.lift' ρ := (varSpine_inj (VExpr.app.inj hr).1).symm
    obtain ⟨_, _, hf, -⟩ := ht.app_inv henv hΓ'
    obtain ⟨T', hT'⟩ := varSpine_fn_typed hΓ' hf
    refine ⟨0, [], Nat.zero_le _, W, hΓ', ?_⟩
    simp only [List.length_nil, Lift.skipN, List.nil_append]
    rw [← hee]
    exact .refl hT'
  | appDF _ hf₁ _ ha₁ _ H₁ _ =>
    cases hl; cases hr
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := ih _ (by omega) W hΓ' (not_isProof_fn hΓ' hf₁ ha₁ hn) H₁
    exact ⟨k, Δ, by omega, W', hΓ'', H'⟩
  | @etaBoth _ _ A B _ _ he _ Hb =>
    subst hl hr
    obtain ⟨⟨_, hA⟩, -⟩ := (he.isType henv.ordered hΓ').forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ') (Params.env.IsType univs) := ⟨hΓ', _, hA⟩
    change A :: Γ' ⊢ (varSpine (e.lift' ρ) (v :: vs)).lift.app (.bvar 0) ≡ₛ[_]
      (varSpine (e'.lift' ρ) (v :: vs)).lift.app (.bvar 0) at Hb
    rw [varSpine_lift, varSpine_lift] at Hb
    have hn' : ¬ IsProof (A :: Γ') (varSpine (e.lift' ρ.skip) (0 :: (v :: vs).map (· + 1))) := by
      intro hp
      change IsProof (A :: Γ') (.app (varSpine (e.lift' ρ.skip) ((v :: vs).map (· + 1))) (.bvar 0))
        at hp
      rw [← varSpine_lift] at hp
      exact hn (IsProof.of_etaBody hΓ' he hp)
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ :=
      ih _ (by omega) (W.skip (A := A)) hΓA hn'
        (show (A :: Γ') ⊢ varSpine (e.lift' ρ.skip) (0 :: (v :: vs).map (· + 1)) ≡ₛ[_]
          varSpine (e'.lift' ρ.skip) (0 :: (v :: vs).map (· + 1)) from Hb)
    refine ⟨k, Δ ++ [A], by omega, ?_, ?_, ?_⟩
    all_goals simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append, ← Lift.skipN_succ']
    · exact W'
    · exact hΓ''
    · exact H'
  | proofIrrel hp hl' _ => subst hl; exact (hn ⟨_, hl', hp⟩).elim
  | sortDF => cases hl
  | constDF => cases hl
  | projDF => cases hl
  | lamDF => cases hl
  | forallEDF => cases hl
  | etaL => cases hl
  | etaR => cases hr

/-! ## The descent -/

/-- **Descent of a hybrid normal equality between lifts**, by strong induction on the
comparison index, in two modes: mode 2 (the two terms are typed below at convertible types)
and mode 0 (no type equality assumed; both terms non-lambda and the left not a proof). No hypothesis on the
environment beyond well-formedness. -/
theorem HybridNormal.descend : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {a b A B : VExpr},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Γ ⊢ a : A → Γ ⊢ b : B → Γ' ⊢ a.lift' ρ ≡ₛ[n] b.lift' ρ →
    (Γ ⊢ A ≡ B → Γ ⊢ a ≡ b) ∧ (¬ IsLam a → ¬ IsLam b → ¬ IsProof Γ a → Γ ⊢ a ≡ b) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro ρ Γ Γ' a b A B W hΓ hΓ' ha hb H
  suffices core : ¬ IsProof Γ a → (Γ ⊢ A ≡ B ∨ (¬ IsLam a ∧ ¬ IsLam b)) → Γ ⊢ a ≡ b by
    refine ⟨fun hAB => ?_, fun h1 h2 h3 => core h3 (.inr ⟨h1, h2⟩)⟩
    by_cases hp : IsProof Γ a
    · exact IsProof.descend hΓ hp ha hb hAB
    · exact core hp (.inl hAB)
  intro hna hside
  have lamSide : IsLam a ∨ IsLam b → Γ ⊢ A ≡ B := fun h =>
    hside.elim id fun ⟨h1, h2⟩ => (h.elim h1 h2).elim
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  cases H with
  | refl _ =>
    cases lift'_inj.1 (hl.trans hr.symm)
    exact ⟨_, ha⟩
  | sortDF h1 h2 h3 =>
    cases lift'_eq_sort hl; cases lift'_eq_sort hr
    exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    cases lift'_eq_const hl; cases lift'_eq_const hr
    exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF hfn _ _ _ _ Hf Hx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨A₁, B₁, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨A₂, B₂, hf', hx'⟩ := hb.app_inv henv hΓ
    have hnf : ¬ IsProof Γ f := not_isProof_fn hΓ hf hx hna
    have hff := hfn.elim
      (fun ⟨hnl₁, hnl₂⟩ => (ih _ (by omega) W hΓ hΓ' hf hf' Hf).2
        (fun h => hnl₁ (IsLam.lift'_iff.2 h)) (fun h => hnl₂ (IsLam.lift'_iff.2 h)) hnf)
      (fun ⟨_, Hcert⟩ => (DomainNormal.descend _ W hΓ hΓ' hf hf' Hcert).2 hnf)
    have hfPi : Γ ⊢ f ≡ f' : .forallE A₁ B₁ := hff.of_l henv hΓ hf
    obtain ⟨⟨u, hA₁₂⟩, -⟩ := (hfPi.uniqU henv hΓ hf').forallE_inv henv hΓ
    have hxx := (ih _ (by omega) W hΓ hΓ' hx hx' Hx).1 ⟨_, hA₁₂⟩
    exact ⟨_, IsDefEq.appDF hfPi (hxx.of_l henv hΓ hx)⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel, hinfo, hlevels,
      huvars, hparams, hindices, hfield, hfieldTyping, hmajor, hclosed, hguard⟩ :=
      ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor', _, _⟩ := hb.proj_inv henv hΓ
    have hm := hmajor.hasType.2
    have hm' := hmajor'.hasType.2
    have hmm := (ih _ (by omega) W hΓ hΓ' hm hm' Hm).2 (not_isLam_major hΓ ha)
      (not_isLam_major hΓ hb) (not_isProof_major hΓ ha hna)
    have h2 := hmajor.trans_l henv hΓ (hmm.of_l henv hΓ hm)
    exact ⟨_, IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping hmajor h2
      hclosed hguard⟩
  | lamDF hA₁ _ Hb =>
    obtain ⟨A₀, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨A₂, b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    have hAB := lamSide (.inl trivial)
    obtain ⟨B₁, hPi₁, hb₁⟩ := ha.lam_inv_forallE henv hΓ
    obtain ⟨B₂, hPi₂, hb₂⟩ := hb.lam_inv_forallE henv hΓ
    have hPiPi : Γ ⊢ .forallE A₀ B₁ ≡ .forallE A₂ B₂ :=
      (hPi₁.trans henv hΓ hAB).trans henv hΓ hPi₂.symm
    obtain ⟨⟨u, hA₀₂⟩, v, hB₁₂⟩ := hPiPi.forallE_inv henv hΓ
    have hA₀ := hA₀₂.hasType.1
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA₀.weak' henv W⟩
    have hb₂' : A₀ :: Γ ⊢ b₂ : B₂ := hb₂.defeqDFC henv (.succ .zero hA₀₂.symm)
    have Hb' := Hb.defeqDFC hΓ' (.succ .zero hA₁)
    have hbb := (ih _ (by omega) (W.cons (A := A₀)) hΓA hΓA' hb₁ hb₂' Hb').1 ⟨_, hB₁₂⟩
    exact ⟨_, IsDefEq.lamDF hA₀₂ (hbb.of_l henv hΓA hb₁)⟩
  | forallEDF hA₁ HA hB₁' Hb =>
    obtain ⟨A₀, B₁, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨A₂, B₂, rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨u₀, hA₀⟩, v₀, hB₁⟩ := ha.forallE_inv henv.ordered
    obtain ⟨⟨u₂, hA₂⟩, v₂, hB₂⟩ := hb.forallE_inv henv.ordered
    have hAA' : Γ' ⊢ A₀.lift' ρ ≡ A₂.lift' ρ := HA.defeq hΓ'
    have hu : u₀ ≈ u₂ := ((hAA'.of_l henv hΓ' (hA₀.weak' henv W)).uniqU henv hΓ'
      (hA₂.weak' henv W)).sort_inv henv hΓ'
    have hA₂u : Γ ⊢ A₂ : .sort u₀ :=
      (IsDefEq.sortDF (hA₂.sort_r henv.ordered hΓ) (hA₀.sort_r henv.ordered hΓ) hu.symm).defeq hA₂
    have hAA := (ih _ (by omega) W hΓ hΓ' hA₀ hA₂u HA).1 ⟨_, HasType.sort (hA₀.sort_r henv.ordered hΓ)⟩
    have hA₀₂ : Γ ⊢ A₀ ≡ A₂ : .sort u₀ := hAA.of_l henv hΓ hA₀
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u₀, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u₀, hA₀.weak' henv W⟩
    have hB₂' : A₀ :: Γ ⊢ B₂ : .sort v₂ := hB₂.defeqDFC henv (.succ .zero hA₀₂.symm)
    have Hb' := Hb.defeqDFC hΓ' (.succ .zero hA₁)
    have hBB' : A₀.lift' ρ :: Γ' ⊢ B₁.lift' ρ.cons ≡ B₂.lift' ρ.cons := Hb'.defeq hΓA'
    have hv : v₀ ≈ v₂ := ((hBB'.of_l henv hΓA' (hB₁.weak' henv W.cons)).uniqU henv hΓA'
      (hB₂'.weak' henv W.cons)).sort_inv henv hΓA'
    have hB₂v : A₀ :: Γ ⊢ B₂ : .sort v₀ :=
      (IsDefEq.sortDF (hB₂'.sort_r henv.ordered hΓA) (hB₁.sort_r henv.ordered hΓA) hv.symm).defeq hB₂'
    have hBB := (ih _ (by omega) W.cons hΓA hΓA' hB₁ hB₂v Hb').1
      ⟨_, HasType.sort (hB₁.sort_r henv.ordered hΓA)⟩
    exact ⟨_, IsDefEq.forallEDF hA₀₂ (hBB.of_l henv hΓA hB₁)⟩
  | etaL he' Hb =>
    obtain ⟨A₀, e₀, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    subst hr
    have hAB := lamSide (.inl trivial)
    obtain ⟨B₁, hPi₁, he₀⟩ := ha.lam_inv_forallE henv hΓ
    have hbPi : Γ ⊢ b : .forallE A₀ B₁ := hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hPi₁.symm)
    obtain ⟨⟨u, hA₀⟩, -⟩ := (hbPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA₀.weak' henv W⟩
    have hbody : A₀ :: Γ ⊢ .app b.lift (.bvar 0) : B₁ := by
      have := HasType.app (hbPi.weak henv.ordered (B := A₀)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using this
    have Hb' := Hb
    rw [show (b.lift' ρ).lift.app (.bvar 0) = (VExpr.app b.lift (.bvar 0)).lift' ρ.cons by
      simp [lift', lift_lift'_cons]] at Hb'
    obtain ⟨w, hB₁s⟩ := he₀.isType henv.ordered hΓA
    have hee := (ih _ (by omega) W.cons hΓA hΓA' he₀ hbody Hb').1 ⟨_, hB₁s⟩
    have h1 : Γ ⊢ .lam A₀ e₀ ≡ .lam A₀ (.app b.lift (.bvar 0)) : .forallE A₀ B₁ :=
      .lamDF hA₀ (hee.of_l henv hΓA he₀)
    exact ⟨_, h1.trans (IsDefEq.eta hbPi)⟩
  | etaR he Hb =>
    obtain ⟨A₂, e₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    subst hl
    have hAB := lamSide (.inr trivial)
    obtain ⟨B₂, hPi₂, he₂⟩ := hb.lam_inv_forallE henv hΓ
    have haPi : Γ ⊢ a : .forallE A₂ B₂ := ha.defeqU_r henv hΓ (hAB.trans henv hΓ hPi₂.symm)
    obtain ⟨⟨u, hA₂⟩, -⟩ := (haPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A₂ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA₂⟩
    have hΓA' : OnCtx (A₂.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA₂.weak' henv W⟩
    have hbody : A₂ :: Γ ⊢ .app a.lift (.bvar 0) : B₂ := by
      have := HasType.app (haPi.weak henv.ordered (B := A₂)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using this
    have Hb' := Hb
    rw [show (a.lift' ρ).lift.app (.bvar 0) = (VExpr.app a.lift (.bvar 0)).lift' ρ.cons by
      simp [lift', lift_lift'_cons]] at Hb'
    obtain ⟨w, hB₂s⟩ := he₂.isType henv.ordered hΓA
    have hnb : ¬ IsProof (A₂ :: Γ) (.app a.lift (.bvar 0)) := fun hp =>
      hna (IsProof.of_etaBody hΓ haPi hp)
    have hee := (ih _ (by omega) W.cons hΓA hΓA' hbody he₂ Hb').1 ⟨_, hB₂s⟩
    have h1 : Γ ⊢ .lam A₂ (.app a.lift (.bvar 0)) ≡ .lam A₂ e₂ : .forallE A₂ B₂ :=
      .lamDF hA₂ (hee.of_l henv hΓA hbody)
    exact ⟨_, (IsDefEq.eta haPi).symm.trans h1⟩
  | @etaBoth _ _ Ad Bd _ _ he he' Hb =>
    subst hl hr
    obtain ⟨⟨u, hAd⟩, -⟩ := (he.isType henv.ordered hΓ').forallE_inv henv.ordered
    have hΓA' : OnCtx (Ad :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hAd⟩
    have hn' : ¬ IsProof (Ad :: Γ') (varSpine (a.lift' ρ.skip) [0]) := by
      intro hp
      change IsProof (Ad :: Γ') (.app (a.lift' ρ.skip) (.bvar 0)) at hp
      rw [← lift_lift'_skip] at hp
      obtain ⟨P, hp, hP⟩ := IsProof.of_etaBody hΓ' he hp
      exact hna (IsProof.of_lift hΓ hΓ' W ha hP hp)
    have Hb' := Hb
    rw [show (a.lift' ρ).lift.app (.bvar 0) = varSpine (a.lift' ρ.skip) [0] by
        simp [varSpine, lift_lift'_skip],
      show (b.lift' ρ).lift.app (.bvar 0) = varSpine (b.lift' ρ.skip) [0] by
        simp [varSpine, lift_lift'_skip]] at Hb'
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := HybridNormal.spine_inv _ (W.skip (A := Ad)) hΓA' hn' Hb'
    have := ih k (by omega) W' hΓ hΓ'' ha hb H'
    exact hside.elim this.1 fun ⟨h1, h2⟩ => this.2 h1 h2 hna
  | proofIrrel hp hl' _ =>
    subst hl
    exact (hna (IsProof.of_lift hΓ hΓ' W ha hp hl')).elim

/-- Every recursively certified comparison embeds in the eta-aware selective
relation. Its lambda domains need no certificate at this outer comparison node. -/
theorem DomainNormal.toHybrid (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DomainNormal n Γ a b) : ∃ m, HybridNormal m Γ a b := by
  induction H with
  | refl h => exact ⟨_, .refl h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 h3 h4 Hf _ ihf iha =>
    obtain ⟨_, HF⟩ := ihf hΓ
    obtain ⟨_, HA⟩ := iha hΓ
    exact ⟨_, .appDF (.inr ⟨_, Hf⟩) h1 h2 h3 h4 HF HA⟩
  | projDF h _ ih =>
    obtain ⟨_, HM⟩ := ih hΓ
    exact ⟨_, .projDF h HM⟩
  | lamDF hA HA _ _ ihb =>
    obtain ⟨_, HB⟩ := ihb ⟨hΓ, _, hA⟩
    exact ⟨_, .lamDF hA ((HA.defeq hΓ).of_l henv hΓ hA) HB⟩
  | forallEDF hA _ hB _ ihA ihB =>
    obtain ⟨_, HA⟩ := ihA hΓ
    obtain ⟨_, HB⟩ := ihB ⟨hΓ, _, hA⟩
    exact ⟨_, .forallEDF hA HA hB HB⟩
  | proofIrrel hP ha hb => exact ⟨_, .proofIrrel hP ha hb⟩

/-- A join whose reducts are obtained below and whose lifted comparison is selective
already descends. What remains missing for strengthening is construction of such
joins for arbitrary lifted declarative equalities; this theorem does not assume or
claim that this construction is a strictly smaller obligation than the typed front. -/
theorem HybridNormal.descend_join (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hQ : Params.env.IsType univs Γ Q) (ha : Γ ⊢ a : T) (hb : Γ ⊢ b : T)
    (Ra : FullReduction Γ a a') (Rb : FullReduction Γ b b')
    (H : HybridNormal n (Q :: Γ) a'.lift b'.lift) : Γ ⊢ a ≡ b : T := by
  have ha' := Ra.hasType hΓ ha
  have hb' := Rb.hasType hΓ hb
  have hΓ' : OnCtx (Q :: Γ) (Params.env.IsType univs) := ⟨hΓ, hQ⟩
  rw [lift_eq_lift', lift_eq_lift'] at H
  obtain ⟨u, hT⟩ := ha.isType henv.ordered hΓ
  have h := (HybridNormal.descend n (Ctx.Lift'.skip (A := Q) .refl) hΓ hΓ' ha' hb' H).1 ⟨_, hT⟩
  exact (Ra.defeq hΓ ha).trans ((h.of_l henv hΓ ha').trans (Rb.defeq hΓ hb).symm)

end Lean4Lean.VEnv.Strengthening
