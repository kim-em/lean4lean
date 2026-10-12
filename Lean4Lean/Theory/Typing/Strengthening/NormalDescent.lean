import Lean4Lean.Theory.Typing.Strengthening.Closures

/-! # Descent of normal equalities between lifts

Route A's descent of the Church-Rosser join. For terms `a`, `b` typed in `Γ` whose lifts along
an arbitrary renaming `Ctx.Lift' ρ Γ Γ'` are *normally* equal in `Γ'` (`NormalEqN`), the
equation descends to `Γ` by induction on the comparison index, in two modes:

* **mode 2** (common type): `a` and `b` are typed below at convertible types. Proof pairs are
  discharged by proof irrelevance below (the common type is a proposition below because sort
  levels are context-free); `lamDF` domains agree below by `Π`-injectivity; the non-lambda side
  of an `etaL`/`etaR` node has the `Π` type below.
* **mode 0** (no type information): the function position of an application, the major of a
  projection, and the spines peeled from an `etaBoth` body. Along such positions nothing is a
  proof (a `Π` into `Prop` is a `Prop`; the projection of a proof is a proof), and, if the
  compared terms have no head β-redex, nothing is a lambda.

The `appDF` case descends the function pair in mode 0, reads the agreement of the argument
types below from unique typing, and descends the argument pair in mode 2. The `etaBoth` case
peels its body, a comparison of fresh-variable spines, down to a comparison of the further
lifted pair at a smaller index (`NormalEqN.spine_inv`); this is why the statement is for
arbitrary renamings.

**Result** (`NormalEqS.descend`): a *strict* normal equality (`NormalEqS`: `NormalEqN` whose
application congruences have non-lambda functions, so that no node compares a lambda with
anything in function position) between lifts of terms typed below descends with no hypothesis
on the environment beyond well-formedness: no canonical `Eq`, no typed front. Hence
(`typedFront_of_strictJoinRepair`) the typed front follows from `StrictJoinRepair`: the join
of a lifted equation can be chosen with lifted reducts and a strict normal equality. The one
configuration a join can put in the way is therefore a lambda in function position of a
congruence: a matched pair of head β-redexes `(λ h : A₁. s₁) x ≡ₚ (λ h : A₂. s₂) y` (or an eta
node between a lambda and the function of a congruence), whose domains `A₁`, `A₂` are types
below with convertible lifts and nothing else to relate them when the arguments are proofs
or functions. Confluence does not produce β-normal joins (the calculus does not normalise),
which is exactly where the route stops; see `STRENGTHENING_LOG.md`. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ[" n "] " e2:30 => NormalEqN true n Γ e1 e2

/-! ## Syntactic predicates -/

/-- The term is a lambda. -/
def IsLam : VExpr → Prop
  | .lam .. => True
  | _ => False

/-- The term is a proof in `Γ`: typed at a proposition. -/
def IsProof (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ P, Γ ⊢ e : P ∧ Γ ⊢ P : .sort .zero

omit [VEnv.Params] in
theorem IsLam.lift'_iff {e : VExpr} {ρ : Lift} : IsLam (e.lift' ρ) ↔ IsLam e := by
  cases e <;> simp [IsLam, lift']

/-! ## Shape inversion of lifts -/

omit [VEnv.Params] in
theorem lift'_eq_app {e f a : VExpr} {ρ : Lift} (h : e.lift' ρ = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f = f₀.lift' ρ ∧ a = a₀.lift' ρ := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_lam {e A b : VExpr} {ρ : Lift} (h : e.lift' ρ = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A = A₀.lift' ρ ∧ b = b₀.lift' ρ.cons := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_forallE {e A B : VExpr} {ρ : Lift} (h : e.lift' ρ = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_proj {e m : VExpr} {S : Name} {i : Nat} {ρ : Lift}
    (h : e.lift' ρ = .proj S i m) : ∃ m₀, e = .proj S i m₀ ∧ m = m₀.lift' ρ := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_sort {e : VExpr} {u : VLevel} {ρ : Lift} (h : e.lift' ρ = .sort u) :
    e = .sort u := by
  cases e <;> simp [lift'] at h
  subst h; rfl

omit [VEnv.Params] in
theorem lift'_eq_const {e : VExpr} {c : Name} {ls : List VLevel} {ρ : Lift}
    (h : e.lift' ρ = .const c ls) : e = .const c ls := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

omit [VEnv.Params] in
theorem lift_lift'_cons (e : VExpr) (ρ : Lift) : e.lift.lift' ρ.cons = (e.lift' ρ).lift := by
  rw [lift_eq_lift', ← lift'_comp, lift_eq_lift', ← lift'_comp]
  simp [Lift.comp]

/-! ## Proofs, sorts and lifts -/

/-- Sort levels are context-free: a type typed below whose lift is a proposition above is a
proposition below. -/
theorem HasType.prop_of_lift_prop (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (hA : Γ ⊢ A : .sort u) (hP : Γ' ⊢ P : .sort .zero) (h : Γ' ⊢ A.lift' ρ ≡ P) :
    Γ ⊢ A : .sort .zero := by
  have hA' : Γ' ⊢ A.lift' ρ : .sort u := hA.weak' henv W
  have hu := (h.of_l henv hΓ' hA' |>.uniqU henv hΓ' hP).sort_inv henv hΓ'
  exact (IsDefEq.sortDF (hA.sort_r henv.ordered hΓ) (by trivial) hu).defeq hA

/-- A term typed below whose lift is a proof above is a proof below. -/
theorem IsProof.of_lift (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (he : Γ ⊢ e : A) (hP : Γ' ⊢ P : .sort .zero) (hp : Γ' ⊢ e.lift' ρ : P) : IsProof Γ e := by
  have he' : Γ' ⊢ e.lift' ρ : A.lift' ρ := he.weak' henv W
  obtain ⟨u, hA⟩ := he.isType henv.ordered hΓ
  exact ⟨A, he, HasType.prop_of_lift_prop hΓ hΓ' W hA hP (he'.uniqU henv hΓ' hp)⟩

/-- A proof below is a proof above. -/
theorem IsProof.lift' (W : Ctx.Lift' ρ Γ Γ') (h : IsProof Γ e) : IsProof Γ' (e.lift' ρ) :=
  let ⟨P, he, hP⟩ := h
  ⟨P.lift' ρ, he.weak' henv W, hP.weak' henv W⟩

/-- Proofness transfers across a conversion with a term typed below. -/
theorem IsProof.transfer (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : IsProof Γ a) (hb : Γ ⊢ b : B) (hab : Γ' ⊢ a.lift' ρ ≡ b.lift' ρ) : IsProof Γ b := by
  obtain ⟨P, haP, hP⟩ := ha
  have haP' : Γ' ⊢ a.lift' ρ : P.lift' ρ := haP.weak' henv W
  have hP' : Γ' ⊢ P.lift' ρ : .sort .zero := hP.weak' henv W
  exact IsProof.of_lift hΓ hΓ' W hb hP' (hab.of_l henv hΓ' haP').hasType.2

/-- A pair of proofs typed below at convertible types is convertible below. -/
theorem IsProof.descend (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ha : IsProof Γ a) (haA : Γ ⊢ a : A) (hb : Γ ⊢ b : B) (hAB : Γ ⊢ A ≡ B) : Γ ⊢ a ≡ b := by
  obtain ⟨P, haP, hP⟩ := ha
  have hAP := haA.uniqU henv hΓ haP
  have hbP : Γ ⊢ b : P := hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP)
  exact ⟨_, .proofIrrel hP haP hbP⟩

/-- The function of a non-proof application is not a proof. -/
theorem IsProof.app_fn (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (ha : Γ ⊢ a : A) (hp : IsProof Γ f) :
    IsProof Γ (.app f a) := by
  obtain ⟨P, hfP, hP⟩ := hp
  obtain ⟨⟨u, hA⟩, v, hB⟩ := (hf.isType henv.ordered hΓ).forallE_inv henv.ordered
  have hPi : Γ ⊢ .forallE A B : .sort (.imax u v) := .forallE hA hB
  have hPiP : Γ ⊢ .forallE A B : .sort .zero := hP.defeqU_l henv hΓ (hfP.uniqU henv hΓ hf)
  have huv := (hPi.uniqU henv hΓ hPiP).sort_inv henv hΓ
  have hv : v ≈ .zero := VLevel.imax_eq_zero.1 huv
  have hBa : Γ ⊢ B.inst a : .sort v := hB.instN henv.ordered Ctx.InstN.zero ha
  have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
  exact ⟨_, hf.app ha, (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA) (by trivial) hv).defeq hBa⟩

theorem not_isProof_fn (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (ha : Γ ⊢ a : A) (hn : ¬ IsProof Γ (.app f a)) : ¬ IsProof Γ f :=
  fun h => hn (IsProof.app_fn hΓ hf ha h)

/-- The major of a non-proof projection is not a proof. -/
theorem not_isProof_major (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : Γ ⊢ .proj S i m : T) (hn : ¬ IsProof Γ (.proj S i m)) : ¬ IsProof Γ m :=
  fun ⟨_, hmP, hP⟩ => hn ⟨T, hp, hp.proj_result_prop_of_major_proof henv hΓ hP hmP⟩

/-- A lambda is not typed at a rigid structure family. -/
theorem not_isLam_major (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : Γ ⊢ .proj S i m : T) : ¬ IsLam m := by
  intro hl
  obtain ⟨A, b, rfl⟩ : ∃ A b, m = .lam A b := by cases m <;> simp [IsLam] at hl; exact ⟨_, _, rfl⟩
  obtain ⟨info, levels, params, indexArgs, sourceMajor, _, _, hinfo, _, _, _, _, _, _, hmajor, _, _⟩ :=
    hp.proj_inv henv hΓ
  obtain ⟨B, hPi, -⟩ := hmajor.hasType.2.lam_inv_forallE henv hΓ
  have hS : Γ ⊢ VExpr.mkApps (.const S levels) (params ++ indexArgs) : .sort _ :=
    (hmajor.isType henv.ordered hΓ).choose_spec
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hinfo) hS hPi.symm

/-! ## Strict normal equality -/

/-- Normal equality (with eta) whose application congruences have non-lambda functions: the
constructors of `NormalEqN true` with `¬ IsLam f₁ → ¬ IsLam f₂ →` added to `appDF`. A matched
pair of head β-redexes, or an eta node between a lambda and the function of a congruence, has
no strict derivation except by `refl`. -/
inductive NormalEqS : Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → NormalEqS 0 Γ e e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → NormalEqS 0 Γ (.sort l₁) (.sort l₂)
  | constDF :
    Params.env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    NormalEqS 0 Γ (.const c ls) (.const c ls')
  | appDF :
    ¬ IsLam f₁ → ¬ IsLam f₂ →
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    NormalEqS n₁ Γ f₁ f₂ → NormalEqS n₂ Γ a₁ a₂ →
    NormalEqS (n₁ + n₂ + 1) Γ (.app f₁ a₁) (.app f₂ a₂)
  | projDF :
    Γ ⊢ .proj typeName index major : resultType →
    NormalEqS n Γ major major' →
    NormalEqS (n + 1) Γ (.proj typeName index major) (.proj typeName index major')
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    NormalEqS n (A::Γ) body₁ body₂ →
    NormalEqS (n + 1) Γ (.lam A₁ body₁) (.lam A₂ body₂)
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → NormalEqS n₁ Γ A₁ A₂ →
    A::Γ ⊢ B₁ : .sort v → NormalEqS n₂ (A::Γ) B₁ B₂ →
    NormalEqS (n₁ + n₂ + 1) Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | etaL :
    Γ ⊢ e' : .forallE A B →
    NormalEqS n (A::Γ) e (.app e'.lift (.bvar 0)) →
    NormalEqS (n + 2) Γ (.lam A e) e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    NormalEqS n (A::Γ) (.app e'.lift (.bvar 0)) e →
    NormalEqS (n + 2) Γ e' (.lam A e)
  | etaBoth :
    Γ ⊢ e : .forallE A B → Γ ⊢ e' : .forallE A B →
    NormalEqS n (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
    NormalEqS (n + 2) Γ e e'
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    NormalEqS 0 Γ h h'

local notation:65 Γ " ⊢ " e1 " ≡ₛ[" n "] " e2:30 => NormalEqS n Γ e1 e2

theorem NormalEqS.toNormalEqN (H : Γ ⊢ e1 ≡ₛ[n] e2) : Γ ⊢ e1 ≡ₚ[n] e2 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 ih1 ih2
  | projDF h _ ih => exact .projDF h ih
  | lamDF h1 h2 _ ih => exact .lamDF h1 h2 ih
  | forallEDF h1 _ h3 _ ih1 ih2 => exact .forallEDF h1 ih1 h3 ih2
  | etaL h _ ih => exact .etaL h ih
  | etaR h _ ih => exact .etaR h ih
  | etaBoth h1 h2 _ ih => exact .etaBoth h1 h2 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3

theorem NormalEqS.defeq (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : Γ ⊢ e1 ≡ₛ[n] e2) :
    Γ ⊢ e1 ≡ e2 := H.toNormalEqN.defeq hΓ

/-- Context conversion (as `NormalEqN.defeqDFC`). -/
theorem NormalEqS.defeqDFC (H₀ : OnCtx Γ₀ (Params.env.IsType univs))
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₛ[m] e2) : Γ₂ ⊢ e1 ≡ₛ[m] e2 := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF hn1 hn2 h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF hn1 hn2 (.defeqDFC henv W h1) (.defeqDFC henv W h2)
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

/-- **Peeling a spine comparison.** A strict normal equality between two variable spines of
lifts (same variables, not a proof) at index `n` yields a strict normal equality between the two
lifts, further lifted along the binders the peeling introduced, at an index at most `n`. The
`etaBoth` case extends the spine by a fresh variable and decreases the index; the `appDF` case
shortens it. -/
theorem NormalEqS.spine_inv : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {e e' : VExpr} {vs : List Nat},
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
  | appDF _ _ hf₁ _ ha₁ _ H₁ _ =>
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

/-- **Descent of a strict normal equality between lifts**, by strong induction on the
comparison index, in two modes: mode 2 (the two terms are typed below at convertible types)
and mode 0 (no type information, both terms non-lambda non-proof). No hypothesis on the
environment beyond well-formedness. -/
theorem NormalEqS.descend : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {a b A B : VExpr},
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
  | appDF hnl₁ hnl₂ _ _ _ _ Hf Hx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨A₁, B₁, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨A₂, B₂, hf', hx'⟩ := hb.app_inv henv hΓ
    have hnf : ¬ IsProof Γ f := not_isProof_fn hΓ hf hx hna
    have hff := (ih _ (by omega) W hΓ hΓ' hf hf' Hf).2
      (fun h => hnl₁ (IsLam.lift'_iff.2 h)) (fun h => hnl₂ (IsLam.lift'_iff.2 h)) hnf
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
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := NormalEqS.spine_inv _ (W.skip (A := Ad)) hΓA' hn' Hb'
    have := ih k (by omega) W' hΓ hΓ'' ha hb H'
    exact hside.elim this.1 fun ⟨h1, h2⟩ => this.2 h1 h2 hna
  | proofIrrel hp hl' _ =>
    subst hl
    exact (hna (IsProof.of_lift hΓ hΓ' W ha hp hl')).elim

end Lean4Lean.VEnv.Strengthening

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr

/-- **The residual obligation of route A.** The join of a lifted equation between terms typed
below at a common type can be chosen with lifted reducts and a *strict* normal equality (no
lambda in function position of a congruence). Confluence (`WF.church_rosser`) gives a join whose
reducts need not be lifts (eta annotations) and whose normal equality need not be strict: the
missing step is the elimination of matched head β-redex pairs and of eta nodes between a lambda
and the function of a congruence, i.e. β-normalisation of the join at those positions, which the
calculus does not provide (it does not normalise). The descent below gives
`StrictJoinRepair → TypedFront`; the residual configuration itself (aligning the domains of
two lifted abstractions at such a position) is equivalent to `PropFront`, hence to
`TypedFront` (see the log), so this is a localisation of the open statement, not a weakening. -/
def StrictJoinRepair {E : VEnv} (hE : E.WF) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (E.IsType U) → E.IsType U Γ Q →
    E.HasType U Γ a T → E.HasType U Γ b T →
    E.IsDefEq U (Q :: Γ) a.lift b.lift T.lift →
    ∃ a' b', letI := hE.params U;
      FullReduction Γ a a' ∧ FullReduction Γ b b' ∧ ∃ n, NormalEqS n (Q :: Γ) a'.lift b'.lift

/-- A strict join of a lifted equation descends: the typed front from `StrictJoinRepair`. -/
theorem typedFront_of_strictJoinRepair {E : VEnv} (hE : E.WF) (H : StrictJoinRepair hE) :
    TypedFront E := by
  intro U Γ Q a b T hΓ hQ ha hb hab
  letI := hE.params U
  obtain ⟨a', b', hra, hrb, n, Hn⟩ := H hΓ hQ ha hb hab
  have ha' := hra.hasType hΓ ha
  have hb' := hrb.hasType hΓ hb
  have hΓ' : OnCtx (Q :: Γ) (E.IsType U) := ⟨hΓ, hQ⟩
  rw [lift_eq_lift', lift_eq_lift'] at Hn
  obtain ⟨w, hT⟩ := ha.isType hE.ordered hΓ
  have hab' := (NormalEqS.descend n (Ctx.Lift'.skip (A := Q) .refl) hΓ hΓ' ha' hb' Hn).1 ⟨_, hT⟩
  exact (hra.defeq hΓ ha).trans ((hab'.of_l hE hΓ ha').trans (hrb.defeq hΓ hb).symm)


end Lean4Lean.VEnv.Strengthening
