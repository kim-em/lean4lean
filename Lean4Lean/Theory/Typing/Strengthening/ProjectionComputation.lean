import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadTyping
import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Lowering computational projection paths

This relation adds saturated constructor projection to beta and closed declaration
computation. Its syntax lowers through arbitrary lifts, and every lowered path can
be replayed from its source typing alone. In particular, no ambient field typing
is imported into the smaller context. Eta and pattern unfolding are not included.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Invert a lift of a whole constant application spine, including every argument. -/
theorem lift'_eq_const_spine (h : e.lift' ρ = mkApps (.const c ls) args) :
    ∃ args₀, e = mkApps (.const c ls) args₀ ∧ args = args₀.map (·.lift' ρ) := by
  induction args using List.snoc_induction generalizing e with
  | nil => exact ⟨[], lift'_eq_const h, rfl⟩
  | snoc args a ih =>
    rw [mkApps_snoc] at h
    obtain ⟨f, a₀, rfl, hf, rfl⟩ := lift'_eq_app h
    obtain ⟨args₀, rfl, rfl⟩ := ih hf.symm
    exact ⟨args₀ ++ [a₀], by rw [mkApps_snoc], by simp⟩

/-- Selection from a lifted argument list selects a lifted original argument. -/
theorem getElem?_lift_inv {args : List VExpr} {field : VExpr} {i : Nat} (h : (args.map (·.lift' ρ))[i]? = some field) :
    ∃ field₀, args[i]? = some field₀ ∧ field = field₀.lift' ρ := by
  rw [List.getElem?_map] at h
  cases he : args[i]? with
  | none => simp [he] at h
  | some a => simp only [he, Option.map_some, Option.some.injEq] at h; exact ⟨a, rfl, h.symm⟩

variable [Params]

/-- Context-independent computation with genuine registered, saturated constructor
projections. The source typing needed for a projection is supplied only at replay. -/
inductive ProjectionCompute (D : Definitions) : VExpr → VExpr → Prop where
  | base : Compute D e out → ProjectionCompute D e out
  | trans : ProjectionCompute D a b → ProjectionCompute D b c → ProjectionCompute D a c
  | projIota : env.projections s info → args.length = info.nparams + info.numFields →
      args[info.nparams + index]? = some field →
      ProjectionCompute D (.proj s index (mkApps (.const info.ctorName ls) args)) field
  | app : ProjectionCompute D f f' → ProjectionCompute D a a' →
      ProjectionCompute D (.app f a) (.app f' a')
  | lam : ProjectionCompute D A A' → ProjectionCompute D b b' →
      ProjectionCompute D (.lam A b) (.lam A' b')
  | forallE : ProjectionCompute D A A' → ProjectionCompute D B B' →
      ProjectionCompute D (.forallE A B) (.forallE A' B')
  | proj : ProjectionCompute D m m' → ProjectionCompute D (.proj s i m) (.proj s i m')

/-- Reconstruct all intermediate typings from the source, including the selected
field's dependent type in each projection step. -/
theorem ProjectionCompute.simAt (R : ProjectionCompute D e out)
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out := by
  induction R generalizing Γ with
  | base h => exact h.simAt henv hD hΓ
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | projIota hi hl hg =>
    intro T ht
    exact .projIota hi ht hg (HasType.projIota_field hΓ hi ht hl hg)
  | app _ _ ih1 ih2 => exact .app henv.orderedStrong hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 => exact .lam henv.orderedStrong hΓ (ih1 hΓ) ih2
  | forallE _ _ ih1 ih2 => exact .forallE henv.orderedStrong hΓ (ih1 hΓ) ih2
  | proj _ ih => exact .proj henv.orderedStrong hΓ (ih hΓ)

/-- Every computational projection path starting at a lift is itself a lift.
This is a syntactic theorem: it assumes no typing in either context. -/
theorem ProjectionCompute.lift_inv (R : ProjectionCompute D (e.lift' ρ) out) :
    ∃ e', ProjectionCompute D e e' ∧ out = e'.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | base h =>
    rw [← hsrc] at h
    obtain ⟨e', hr, he⟩ := h.lift_inv
    exact ⟨e', .base hr, he⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1, R1, h1⟩ := ih1 hsrc
    obtain ⟨e2, R2, h2⟩ := ih2 h1.symm
    exact ⟨e2, R1.trans R2, h2⟩
  | projIota hi hl hg =>
    obtain ⟨major, rfl, hm⟩ := lift'_eq_proj hsrc
    obtain ⟨args, rfl, rfl⟩ := lift'_eq_const_spine hm.symm
    obtain ⟨field, hf, he⟩ := getElem?_lift_inv hg
    exact ⟨field, .projIota hi (by simpa using hl) hf, he⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨f', Rf, rfl⟩ := ihf rfl
    obtain ⟨a', Ra, rfl⟩ := iha rfl
    exact ⟨_, .app Rf Ra, rfl⟩
  | proj _ ihm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsrc
    obtain ⟨m', Rm, rfl⟩ := ihm rfl
    exact ⟨_, .proj Rm, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', Rb, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA Rb, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩

/-- Lower a complete path and reconstruct its equality at the original source
type, without an ambient typing premise and without strengthening. -/
theorem ProjectionCompute.descend (R : ProjectionCompute D (e.lift' ρ) out)
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (he : HasType env univs Γ e T) :
    ∃ e', out = e'.lift' ρ ∧ ProjectionCompute D e e' ∧ IsDefEq env univs Γ e e' T := by
  obtain ⟨e', R0, hh⟩ := R.lift_inv
  exact ⟨e', hh, R0, R0.simAt hD hΓ T he⟩

/-- A computational Pi exposure above provides the actual function type below,
including paths which compute through constructor projections. Eta elimination
for this larger operational relation is still needed. -/
theorem ProjectionCompute.function_type_below
    (R : ProjectionCompute D (T.lift' ρ) (.forallE A B))
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') := by
  obtain ⟨out, R0, hh⟩ := R.lift_inv
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE hh.symm
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have HT := R0.simAt hD hΓ (.sort u) hT
  exact ⟨A', B', HT.defeq hf, _, HT⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
