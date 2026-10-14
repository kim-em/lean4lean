import Lean4Lean.Theory.Typing.Strengthening.TypeRecoveryCore

/-! # Compatible eta with recoverable function types

Eta annotations are justified by a source-typed TypeRecovery certificate.
Consequently both the chosen annotations and the expanded term descend through
binder insertion. The base computation is a parameter with checked source-typed descent.
This does not assert coverage of every actual eta or indexed-prefix step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Computation and compatible eta whose chosen Pi typing can be reconstructed
from source well-formedness below. The next stage may use this relation as its computational base. -/
inductive RecoveredEtaWith (C : List VExpr → VExpr → VExpr → Prop) : List VExpr → VExpr → VExpr → Prop where
  | base : C Γ e out → RecoveredEtaWith C Γ e out
  | eta : TypeRecoveryWith C Γ e (.forallE A B) →
      RecoveredEtaWith C Γ e (.lam A (.app e.lift (.bvar 0)))
  | trans : RecoveredEtaWith C Γ a b → RecoveredEtaWith C Γ b c →
      RecoveredEtaWith C Γ a c
  | app : RecoveredEtaWith C Γ f f' → RecoveredEtaWith C Γ a a' →
      RecoveredEtaWith C Γ (.app f a) (.app f' a')
  | lam : RecoveredEtaWith C Γ A A' → RecoveredEtaWith C (A :: Γ) b b' →
      RecoveredEtaWith C Γ (.lam A b) (.lam A' b')
  | forallE : RecoveredEtaWith C Γ A A' → RecoveredEtaWith C (A :: Γ) B B' →
      RecoveredEtaWith C Γ (.forallE A B) (.forallE A' B')
  | proj : RecoveredEtaWith C Γ m m' →
      RecoveredEtaWith C Γ (.proj s i m) (.proj s i m')

/-- Every chosen eta type weakens along with its source certificate. -/
theorem RecoveredEtaWith.weakN (hweak : ComputeWeakening C) (W : Ctx.LiftN n k Γ Γ')
    (R : RecoveredEtaWith C Γ e out) :
    RecoveredEtaWith C Γ' (e.liftN n k) (out.liftN n k) := by
  induction R generalizing k Γ' with
  | base R => exact .base (hweak W R)
  | eta R =>
    simpa only [liftN, liftVar, Nat.zero_lt_succ, if_true, ← lift_liftN'] using
      RecoveredEtaWith.eta (R.weakN hweak W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

variable {e : VExpr} {ρ : Lift}

/-- Every path beginning at a typed lifted source reconstructs an exact lower
result and its equality at the original source type. The eta case recovers its
Pi domain below; it never assumes the expanded term was already typed there. -/
theorem RecoveredEtaWith.descend
    (R : RecoveredEtaWith C Γ' (e.lift' ρ) target)
    (hcompute : ComputeDescent C)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out T := by
  generalize hsource : e.lift' ρ = source at R
  induction R generalizing ρ Γ e T with
  | base R =>
    rw [← hsource] at R
    exact hcompute R W hΓ hΓ' ht
  | eta R =>
    rw [← hsource] at R
    obtain ⟨A, B, rfl, rfl, hf⟩ := R.pi_below hcompute W hΓ hΓ' ⟨_, ht⟩
    refine ⟨.lam A (.app e.lift (.bvar 0)), ?_, ?_⟩
    · simp only [lift', lift_lift'_cons, Lift.liftVar, hsource]
    · exact IsDefEq.trans_l henv hΓ ht (IsDefEq.eta hf).symm
  | trans _ _ ih1 ih2 =>
    obtain ⟨mid, hm, E1⟩ := ih1 W hΓ hΓ' ht hsource
    obtain ⟨out, hout, E2⟩ := ih2 W hΓ hΓ' E1.hasType.2 hm.symm
    exact ⟨out, hout, E1.trans E2⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsource
    obtain ⟨A, B, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', rfl, Ef⟩ := ih1 W hΓ hΓ' hf rfl
    obtain ⟨a', rfl, Ea⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨.app f' a', rfl, IsDefEq.trans_l henv hΓ ht (.appDF Ef Ea)⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsource
    obtain ⟨⟨u, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨A', rfl, EA⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, Eb⟩ := ih2 W.cons ⟨hΓ, _, hA⟩
      ⟨hΓ', _, hA.weak' henv.ordered W⟩ hb rfl
    exact ⟨.lam A' b', rfl, IsDefEq.trans_l henv hΓ ht (.lamDF EA Eb)⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsource
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := HasType.forallE_inv henv.ordered ht
    obtain ⟨A', rfl, EA⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨B', rfl, EB⟩ := ih2 W.cons ⟨hΓ, _, hA⟩
      ⟨hΓ', _, hA.weak' henv.ordered W⟩ hB rfl
    exact ⟨.forallE A' B', rfl, IsDefEq.trans_l henv hΓ ht (.forallEDF EA EB)⟩
  | @proj Γs m m' s i _ ih =>
    obtain ⟨m₀, rfl, rfl⟩ := lift'_eq_proj hsource
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht
    obtain ⟨m₀', rfl, Em⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    refine ⟨.proj s i m₀', rfl, ?_⟩
    exact SimAt.proj henv.orderedStrong hΓ
      (fun _ H => IsDefEq.trans_l henv hΓ H Em) _ ht

/-- Ordinary typed replay follows by taking the context insertion to be identity. -/
theorem RecoveredEtaWith.simAt (R : RecoveredEtaWith C Γ e out)
    (hcompute : ComputeDescent C)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out := by
  intro T ht
  have R' : RecoveredEtaWith C Γ (e.lift' .refl) out := by simpa using R
  obtain ⟨out₀, hout, H⟩ := R'.descend hcompute .refl hΓ hΓ ht
  simp only [lift'_refl] at hout
  exact hout.symm ▸ H

/-- The enlarged computation recovers Pi exposure below, now including eta in
computational bodies when its function type has a recovery certificate. -/
theorem RecoveredEtaWith.pi_exposure_below
    (R : RecoveredEtaWith C Γ' (e.lift' ρ) (.forallE A B))
    (hcompute : ComputeDescent C)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ A₀ B₀, env.IsDefEq univs Γ e (.forallE A₀ B₀) T := by
  obtain ⟨out, hout, H⟩ := R.descend hcompute W hΓ hΓ' ht
  obtain ⟨A₀, B₀, rfl, _, _⟩ := lift'_eq_forallE hout.symm
  exact ⟨A₀, B₀, H⟩

/-- The eta extension preserves the checked descent interface. -/
theorem RecoveredEtaWith.computeDescent (hc : ComputeDescent C) :
    ComputeDescent (RecoveredEtaWith C) :=
  fun R W hΓ hΓ' ht => R.descend hc W hΓ hΓ' ht

/-- Enlarging the computational base also enlarges compatible eta recovery. -/
theorem RecoveredEtaWith.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (R : RecoveredEtaWith C Γ e out) : RecoveredEtaWith C' Γ e out := by
  induction R with
  | base R => exact .base (hC R)
  | eta R => exact .eta (R.mono hC)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

end Lean4Lean.VEnv.Strengthening
