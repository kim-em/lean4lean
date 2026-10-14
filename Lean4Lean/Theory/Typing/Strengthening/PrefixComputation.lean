import Lean4Lean.Theory.Typing.Strengthening.PatternComputation
import Lean4Lean.Theory.Typing.Strengthening.WitnessedPrefixReplay
import Lean4Lean.Theory.Typing.Strengthening.QuotPrefixReplay

/-! # Compatible computation with actual checked prefixes

Concrete pattern computation is extended by the original singleton and quotient
prefix rules, at arbitrary compatible positions and through finite composition.
The witnessed proposition front supplies exact operational reflection for this
whole relation. The front itself and full equality coverage remain unproved.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Finite compatible computation with actual registered prefix checks.
There are no function-eta or structure-eta expansion constructors. -/
inductive PrefixCompute (D : Definitions) : List VExpr → VExpr → VExpr → Prop where
  | base : PatternCompute D a b → PrefixCompute D Γ a b
  | singleton : PrefixUnfold env univs recursorData Γ name levels args out →
      PrefixCompute D Γ (mkApps (.const name levels) args) out
  | quotient : QuotPrefixUnfold env univs Γ levels args out →
      PrefixCompute D Γ (mkApps (.const ``Quot.lift levels) args) out
  | trans : PrefixCompute D Γ a b → PrefixCompute D Γ b c → PrefixCompute D Γ a c
  | app : PrefixCompute D Γ f f' → PrefixCompute D Γ a a' →
      PrefixCompute D Γ (.app f a) (.app f' a')
  | lam : PrefixCompute D Γ A A' → PrefixCompute D (A :: Γ) b b' →
      PrefixCompute D Γ (.lam A b) (.lam A' b')
  | forallE : PrefixCompute D Γ A A' → PrefixCompute D (A :: Γ) B B' →
      PrefixCompute D Γ (.forallE A B) (.forallE A' B')
  | proj : PrefixCompute D Γ m m' → PrefixCompute D Γ (.proj s i m) (.proj s i m')

theorem PrefixCompute.refl : PrefixCompute D Γ e e := .base .refl

/-- Source typing reconstructs every intermediate typing in a compatible path. -/
theorem PrefixCompute.simAt (R : PrefixCompute D Γ a b)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ a b := by
  induction R with
  | base R => exact R.simAt hs hΓ
  | singleton H => intro T ht; exact (H.defeq henv hΓ).of_l henv hΓ ht
  | quotient H => intro T ht; exact (H.defeq henv hΓ).of_l henv hΓ ht
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | app _ _ ih1 ih2 => exact .app henv.orderedStrong hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 => exact .lam henv.orderedStrong hΓ (ih1 hΓ) ih2
  | forallE _ _ ih1 ih2 => exact .forallE henv.orderedStrong hΓ (ih1 hΓ) ih2
  | proj _ ih => exact .proj henv.orderedStrong hΓ (ih hΓ)

/-- The witnessed front reflects every compatible path, retaining an actual
lower computation and the exact lifted target. Source typing suffices; no
lower target typing, eta step, or certificate-completeness premise is added. -/
theorem PrefixCompute.lift_inv (R : PrefixCompute D Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ out, PrefixCompute D Γ e out ∧ target = out.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing ρ Γ e T with
  | base R =>
    rw [← hsrc] at R
    obtain ⟨out, R, hout⟩ := R.lift_inv
    exact ⟨out, .base R, hout⟩
  | singleton H =>
    obtain ⟨args, rfl, rfl⟩ := lift'_eq_const_spine hsrc
    obtain ⟨out, R, hout⟩ := GuardedSingleton.prefix_rule_replay_witnessed
      heq hfront W hΓ hΓ' H ht
    exact ⟨out, .singleton R, hout⟩
  | quotient H =>
    obtain ⟨args, rfl, rfl⟩ := lift'_eq_const_spine hsrc
    obtain ⟨out, R, hout⟩ := quotPrefixUnfold_replay henv hΓ H ht
    exact ⟨out, .quotient R, hout⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨middle, R1, hm⟩ := ih1 W hΓ hΓ' ht hsrc
    obtain ⟨out, R2, hout⟩ := ih2 W hΓ hΓ' (R1.simAt hs hΓ _ ht).hasType.2 hm.symm
    exact ⟨out, R1.trans R2, hout⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', Rf, rfl⟩ := ih1 W hΓ hΓ' hf rfl
    obtain ⟨a', Ra, rfl⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨_, .app Rf Ra, rfl⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsrc
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨A', RA, rfl⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', Rb, rfl⟩ := ih2 W.cons ⟨hΓ, _, hA⟩ ⟨hΓ', _, hA.weak' henv W⟩ hb rfl
    exact ⟨_, .lam RA Rb, rfl⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsrc
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨A', RA, rfl⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨B', RB, rfl⟩ := ih2 W.cons ⟨hΓ, _, hA⟩ ⟨hΓ', _, hA.weak' henv W⟩ hB rfl
    exact ⟨_, .forallE RA RB, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsrc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', Rm, rfl⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨_, .proj Rm, rfl⟩

/-- Conversion of the ambient context preserves the actual checked path.
Source typing is used only to reconstruct intermediate and binder typings. -/
theorem PrefixCompute.defeqDFC (R : PrefixCompute D Γ₁ a b)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (ht : env.HasType univs Γ₁ a T) :
    PrefixCompute D Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | base R => exact .base R
  | singleton H => exact .singleton (H.defeqDFC henv hΓ W)
  | quotient H => exact .quotient (H.defeqDFC henv hΓ W)
  | trans R1 _ ih1 ih2 =>
    exact .trans (ih1 W ht) (ih2 W (R1.simAt hs (W.isType' hΓ) _ ht).hasType.2)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hA) (ih2 (.succ W hA) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (.succ W hA) hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      ht.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)

end Lean4Lean.VEnv.Strengthening.PureObservation
