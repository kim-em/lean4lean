import Lean4Lean.Theory.Typing.Strengthening.CastComputation

/-! # Compatible K computation with endpoint certificates

The matching predicate is explicit. If it descends at common-typed endpoints,
then every compatible computation path replays below from source typing alone.
No completeness of the matching predicate is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)

/-- Binder insertion reflects all six arguments of a canonical Eq.rec. -/
theorem lift'_eq_eqRecApp (h : e.lift' ρ = eqRecApp v w α a M m b p) :
    ∃ α₀ a₀ M₀ m₀ b₀ p₀, e = eqRecApp v w α₀ a₀ M₀ m₀ b₀ p₀ ∧
      α = α₀.lift' ρ ∧ a = a₀.lift' ρ ∧ M = M₀.lift' ρ ∧
      m = m₀.lift' ρ ∧ b = b₀.lift' ρ ∧ p = p₀.lift' ρ := by
  have he := congrArg (fun e => e.subst ρ.inv) h
  simp only [subst_lift', lift_l_inv, subst_id, eqRecApp_subst] at he
  refine ⟨_, _, _, _, _, _, he, ?_⟩
  have hh := h.symm.trans (congrArg (fun e => e.lift' ρ) he)
  rw [eqRecApp_lift'] at hh
  simp only [eqRecApp, VExpr.app.injEq] at hh
  exact ⟨hh.1.1.1.1.1.2, hh.1.1.1.1.2, hh.1.1.1.2,
    hh.1.1.2, hh.1.2, hh.2⟩

variable [Params]

/-- Compatible concrete computation with an explicit endpoint-comparison
certificate at every nonsyntactic K match. Bodies use the source domain. -/
inductive GuardedKCompute (D : Definitions) (Cmp : List VExpr → VExpr → VExpr → Prop) : List VExpr → VExpr → VExpr → Prop where
  | base : CastCompute D e out → GuardedKCompute D Cmp Γ e out
  | eqRec : Cmp Γ a b →
      GuardedKCompute D Cmp Γ (eqRecApp v w α a M m b p) m
  | trans : GuardedKCompute D Cmp Γ a b → GuardedKCompute D Cmp Γ b c → GuardedKCompute D Cmp Γ a c
  | app : GuardedKCompute D Cmp Γ f f' → GuardedKCompute D Cmp Γ a a' →
      GuardedKCompute D Cmp Γ (.app f a) (.app f' a')
  | lam : GuardedKCompute D Cmp Γ A A' → GuardedKCompute D Cmp (A :: Γ) b b' →
      GuardedKCompute D Cmp Γ (.lam A b) (.lam A' b')
  | forallE : GuardedKCompute D Cmp Γ A A' → GuardedKCompute D Cmp (A :: Γ) B B' →
      GuardedKCompute D Cmp Γ (.forallE A B) (.forallE A' B')
  | proj : GuardedKCompute D Cmp Γ m m' → GuardedKCompute D Cmp Γ (.proj s i m) (.proj s i m')

variable {e : VExpr} {ρ : Lift}

/-- Endpoint matching reflects through every binder insertion when both
endpoints have a common type below. This is a property of the supplied concrete
certificate relation, not a premise about arbitrary definitional equality. -/
def EndpointDescent (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {ρ Γ Γ' a b α}, Ctx.Lift' ρ Γ Γ' → OnCtx Γ (env.IsType univs) →
    OnCtx Γ' (env.IsType univs) → env.HasType univs Γ a α → env.HasType univs Γ b α →
    Cmp Γ' (a.lift' ρ) (b.lift' ρ) → env.IsDefEqU univs Γ a b

/-- Endpoint descent restricted to pairs with a canonical Eq witness already
available below the insertion. For arbitrary conversion this is an unproved
front; typing of an Eq.rec source supplies precisely this extra witness. -/
def WitnessedTermDescent (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {ρ Γ Γ' u A a b witness}, Ctx.Lift' ρ Γ Γ' →
    OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    u.WF univs → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ a A → env.HasType univs Γ b A →
    env.HasType univs Γ witness (eqApp u A a b) →
    Cmp Γ' (a.lift' ρ) (b.lift' ρ) → env.IsDefEqU univs Γ a b

theorem WitnessedTermDescent.of_endpoint (H : EndpointDescent Cmp) : WitnessedTermDescent Cmp :=
  fun W hΓ hΓ' _ _ ha hb _ Hcmp => H W hΓ hΓ' ha hb Hcmp

variable {Cmp : List VExpr → VExpr → VExpr → Prop}

/-- Weakening of the matching certificates extends to the whole compatible
computation, with the corresponding context insertion beneath each binder. -/
theorem GuardedKCompute.weakN
    (hcmp : ∀ {n k Γ Γ' a b}, Ctx.LiftN n k Γ Γ' → Cmp Γ a b →
      Cmp Γ' (a.liftN n k) (b.liftN n k))
    (W : Ctx.LiftN n k Γ Γ') (R : GuardedKCompute D Cmp Γ e out) :
    GuardedKCompute D Cmp Γ' (e.liftN n k) (out.liftN n k) := by
  induction R generalizing k Γ' with
  | base R =>
    apply GuardedKCompute.base
    have h := R.subst (σ := Subst.lift_r Subst.id (.consN (.skipN .refl n) k))
    simpa only [← lift_as_subst, lift'_consN_skipN] using h
  | eqRec H => exact .eqRec (hcmp W H)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Scope preservation is syntactic, including the nonlinear matching rule.
No typing or context well-formedness is used in this part. -/
theorem GuardedKCompute.lift_shape (R : GuardedKCompute D Cmp Γ (e.lift' ρ) out) :
    ∃ e' : VExpr, out = e'.lift' ρ := by
  generalize hs : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | base h =>
    rw [← hs] at h
    obtain ⟨e', _, he⟩ := h.lift_inv
    exact ⟨e', he⟩
  | eqRec =>
    obtain ⟨_, _, _, m, _, _, _, _, _, _, hm, _⟩ := lift'_eq_eqRecApp hs
    exact ⟨m, hm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e', he⟩ := ih1 hs
    exact ih2 he.symm
  | app _ _ ih1 ih2 =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hs
    obtain ⟨f', rfl⟩ := ih1 rfl
    obtain ⟨a', rfl⟩ := ih2 rfl
    exact ⟨.app f' a', rfl⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hs
    obtain ⟨A', rfl⟩ := ih1 rfl
    obtain ⟨b', rfl⟩ := ih2 rfl
    exact ⟨.lam A' b', rfl⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hs
    obtain ⟨A', rfl⟩ := ih1 rfl
    obtain ⟨B', rfl⟩ := ih2 rfl
    exact ⟨.forallE A' B', rfl⟩
  | @proj _ _ _ s i _ ih =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hs
    obtain ⟨m', rfl⟩ := ih rfl
    exact ⟨.proj s i m', rfl⟩

/-- Replay a whole compatible path below a binder insertion. The root K case
recovers endpoint typings from the source, then descends its comparison guard.
No equality or typing of the result is assumed below. -/
theorem GuardedKCompute.simAt_below_witnessed (R : GuardedKCompute D Cmp Γ' source target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hcmp : WitnessedTermDescent Cmp)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hsource : e.lift' ρ = source) (htarget : out.lift' ρ = target) :
    env.SimAt univs Γ e out := by
  induction R generalizing Γ ρ e out with
  | base R =>
    rw [← hsource] at R
    obtain ⟨out', R, hout⟩ := R.lift_inv
    have he := lift'_inj.1 (htarget.trans hout)
    subst out'
    exact R.simAt heq hs hΓ
  | eqRec H =>
    obtain ⟨α, a, M, m, b, p, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      lift'_eq_eqRecApp hsource
    have hm := lift'_inj.1 htarget
    subst out
    intro T ht
    obtain ⟨_, hu, hA, ha, _, _, hb, hp⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
    have hab := hcmp W hΓ hΓ' hu hA ha hb hp H
    exact eqRecApp_simAt henv heq hΓ hab T ht
  | trans R1 _ ih1 ih2 =>
    have R1' := R1
    rw [← hsource] at R1'
    obtain ⟨mid, hm⟩ := R1'.lift_shape
    exact (ih1 W hΓ hΓ' hsource hm.symm).trans (ih2 W hΓ hΓ' hm.symm htarget)
  | app _ _ ih1 ih2 =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsource
    obtain ⟨f', a', rfl, rfl, rfl⟩ := lift'_eq_app htarget
    exact SimAt.app henv.orderedStrong hΓ (ih1 W hΓ hΓ' rfl rfl) (ih2 W hΓ hΓ' rfl rfl)
  | lam _ _ ih1 ih2 =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsource
    obtain ⟨A', b', rfl, rfl, rfl⟩ := lift'_eq_lam htarget
    apply SimAt.lam henv.orderedStrong hΓ (ih1 W hΓ hΓ' rfl rfl)
    intro hAb
    exact ih2 W.cons hAb ⟨hΓ', hAb.2.weak' henv.ordered W⟩ rfl rfl
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsource
    obtain ⟨A', B', rfl, rfl, rfl⟩ := lift'_eq_forallE htarget
    apply SimAt.forallE henv.orderedStrong hΓ (ih1 W hΓ hΓ' rfl rfl)
    intro hAb
    exact ih2 W.cons hAb ⟨hΓ', hAb.2.weak' henv.ordered W⟩ rfl rfl
  | @proj _ _ _ s i _ ih =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsource
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj htarget
    exact SimAt.proj henv.orderedStrong hΓ (ih W hΓ hΓ' rfl rfl)

/-- The original stronger interface is a specialization of witnessed replay. -/
theorem GuardedKCompute.simAt_below (R : GuardedKCompute D Cmp Γ' source target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hcmp : EndpointDescent Cmp)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hsource : e.lift' ρ = source) (htarget : out.lift' ρ = target) :
    env.SimAt univs Γ e out :=
  R.simAt_below_witnessed heq hs (WitnessedTermDescent.of_endpoint hcmp) W hΓ hΓ' hsource htarget

/-- Source typing supplies the lower equality proof required by witnessed
matching at every K node, including under binders and through composition. -/
theorem GuardedKCompute.descend_witnessed (R : GuardedKCompute D Cmp Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hcmp : WitnessedTermDescent Cmp)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) :
    ∃ out, target = out.lift' ρ ∧ env.SimAt univs Γ e out := by
  obtain ⟨out, hout⟩ := R.lift_shape
  exact ⟨out, hout, R.simAt_below_witnessed heq hs hcmp W hΓ hΓ' rfl hout.symm⟩

/-- Every guarded computation from a lifted source has a typed replay below. -/
theorem GuardedKCompute.descend (R : GuardedKCompute D Cmp Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hcmp : EndpointDescent Cmp)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) :
    ∃ out, target = out.lift' ρ ∧ env.SimAt univs Γ e out := by
  obtain ⟨out, hout⟩ := R.lift_shape
  exact ⟨out, hout, R.simAt_below heq hs hcmp W hΓ hΓ' rfl hout.symm⟩

/-- Pi exposure in this enlarged fragment recovers the corresponding Pi below.
The exposed domain and codomain need no separate lower-context typing premise. -/
theorem GuardedKCompute.pi_exposure_below
    (R : GuardedKCompute D Cmp Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hcmp : EndpointDescent Cmp)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ A₀ B₀, env.IsDefEq univs Γ e (.forallE A₀ B₀) T := by
  obtain ⟨out, hout, hsim⟩ := R.descend heq hs hcmp W hΓ hΓ'
  obtain ⟨A₀, B₀, rfl, _, _⟩ := lift'_eq_forallE hout.symm
  exact ⟨A₀, B₀, hsim _ ht⟩

end Lean4Lean.VEnv.Strengthening
