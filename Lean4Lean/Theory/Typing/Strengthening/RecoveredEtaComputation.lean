import Lean4Lean.Theory.Typing.Strengthening.TypeRecovery

/-! # Compatible eta with recoverable function types

Eta annotations are justified by a source-typed TypeRecovery certificate.
Consequently both the chosen annotations and the expanded term descend through
binder insertion. The base computations may contain nested certified K guards.
This does not assert coverage of every actual eta or indexed-prefix step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Computation and compatible eta whose chosen Pi typing can be reconstructed
from source well-formedness below. Each computation stage uses a fixed K depth. -/
inductive RecoveredEtaCompute (D : Definitions) (depth : Nat) : List VExpr → VExpr → VExpr → Prop where
  | base : CertifiedKCompute D depth Γ e out → RecoveredEtaCompute D depth Γ e out
  | eta : TypeRecovery D depth Γ e (.forallE A B) →
      RecoveredEtaCompute D depth Γ e (.lam A (.app e.lift (.bvar 0)))
  | trans : RecoveredEtaCompute D depth Γ a b → RecoveredEtaCompute D depth Γ b c →
      RecoveredEtaCompute D depth Γ a c
  | app : RecoveredEtaCompute D depth Γ f f' → RecoveredEtaCompute D depth Γ a a' →
      RecoveredEtaCompute D depth Γ (.app f a) (.app f' a')
  | lam : RecoveredEtaCompute D depth Γ A A' → RecoveredEtaCompute D depth (A :: Γ) b b' →
      RecoveredEtaCompute D depth Γ (.lam A b) (.lam A' b')
  | forallE : RecoveredEtaCompute D depth Γ A A' → RecoveredEtaCompute D depth (A :: Γ) B B' →
      RecoveredEtaCompute D depth Γ (.forallE A B) (.forallE A' B')
  | proj : RecoveredEtaCompute D depth Γ m m' →
      RecoveredEtaCompute D depth Γ (.proj s i m) (.proj s i m')

/-- Identity is included in the computational base. -/
theorem RecoveredEtaCompute.refl : RecoveredEtaCompute D depth Γ e e := .base (.base .refl)

/-- Every chosen eta type weakens along with its source certificate. -/
theorem RecoveredEtaCompute.weakN (W : Ctx.LiftN n k Γ Γ')
    (R : RecoveredEtaCompute D depth Γ e out) :
    RecoveredEtaCompute D depth Γ' (e.liftN n k) (out.liftN n k) := by
  induction R generalizing k Γ' with
  | base R => exact .base (R.weakN (fun W H => KCertificate.weakN W H) W)
  | eta R =>
    simpa only [liftN, liftVar, Nat.zero_lt_succ, if_true, ← lift_liftN'] using
      RecoveredEtaCompute.eta (R.weakN W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

variable {e : VExpr} {ρ : Lift}

/-- Every path beginning at a typed lifted source reconstructs an exact lower
result and its equality at the original source type. The eta case recovers its
Pi domain below; it never assumes the expanded term was already typed there. -/
theorem RecoveredEtaCompute.descend
    (R : RecoveredEtaCompute D depth Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out T := by
  generalize hsource : e.lift' ρ = source at R
  induction R generalizing ρ Γ e T with
  | base R =>
    rw [← hsource] at R
    obtain ⟨out, hout, H⟩ := CertifiedKCompute.descend R heq hs W hΓ hΓ'
    exact ⟨out, hout, H _ ht⟩
  | eta R =>
    rw [← hsource] at R
    obtain ⟨A, B, rfl, rfl, hf⟩ := R.pi_below heq hs W hΓ hΓ' ⟨_, ht⟩
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
theorem RecoveredEtaCompute.simAt (R : RecoveredEtaCompute D depth Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out := by
  intro T ht
  have R' : RecoveredEtaCompute D depth Γ (e.lift' .refl) out := by simpa using R
  obtain ⟨out₀, hout, H⟩ := R'.descend heq hs .refl hΓ hΓ ht
  simp only [lift'_refl] at hout
  exact hout.symm ▸ H

/-- The enlarged computation recovers Pi exposure below, now including eta in
computational bodies when its function type has a recovery certificate. -/
theorem RecoveredEtaCompute.pi_exposure_below
    (R : RecoveredEtaCompute D depth Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ A₀ B₀, env.IsDefEq univs Γ e (.forallE A₀ B₀) T := by
  obtain ⟨out, hout, H⟩ := R.descend heq hs W hΓ hΓ' ht
  obtain ⟨A₀, B₀, rfl, _, _⟩ := lift'_eq_forallE hout.symm
  exact ⟨A₀, B₀, H⟩

end Lean4Lean.VEnv.Strengthening
