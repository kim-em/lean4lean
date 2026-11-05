import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroLambdaReadout

/-! # Marked lambda traces with pending ignored control arguments

The pending argument count distinguishes a payload lambda from a generated
control lambda. No variable or argument observation is used along the control
path. Payloads retain their lower component histories below temporary binders.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open PiOriginObservation (FixedTail)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- A marked lambda is observed after consuming exactly the pending control
arguments. Payload depth counts temporary binders above its original context. -/
inductive IgnoredLambdaTrace (P : ProofShape → ProofShape → Prop) : Nat → ProofShape → Nat → Prop where
  | payload : P A b → IgnoredLambdaTrace P n ((ProofShape.lam A b).liftN n) 0
  | lam : IgnoredLambdaTrace P (n+1) b k → IgnoredLambdaTrace P n (.lam A b) (k+1)
  | app : IgnoredLambdaTrace P n f (k+1) → IgnoredLambdaTrace P n (.app f a) k

/-- Substitution of temporary controls fixes every marked lower payload. -/
theorem IgnoredLambdaTrace.subst (H : IgnoredLambdaTrace P n e k) (HT : FixedTail n m σ) :
    IgnoredLambdaTrace P m (e.subst σ) k := by
  induction H generalizing m σ with
  | payload h => rw [HT.payload]; exact .payload h
  | lam _ ih => exact .lam (ih HT.lift)
  | app _ ih => exact .app (ih HT)

/-- Inserting a temporary binder lifts syntax and payload depth together. -/
theorem IgnoredLambdaTrace.lift (H : IgnoredLambdaTrace P n e k) :
    IgnoredLambdaTrace P (n+1) (e.liftN 1) k := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ H.subst HT

/-- A lifted control path can be read below its fresh unused binder. -/
theorem IgnoredLambdaTrace.of_lift (H : IgnoredLambdaTrace P (n+1) (e.liftN 1) k) :
    IgnoredLambdaTrace P n e k := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  have R := H.subst (HT.cons (a := .proof))
  simpa only [lift_subst_cons, subst_id] using R

/-- A literal lambda at zero pending arity is exactly a lower marked payload. -/
theorem IgnoredLambdaTrace.lam_zero (H : IgnoredLambdaTrace P n (.lam X y) 0) :
    ∃ A b, P A b ∧ X = A.liftN n ∧ y = b.liftN n 1 := by
  cases H with
  | payload HP => exact ⟨_, _, HP, rfl, rfl⟩

/-- A literal lambda at positive pending arity is a control frame. -/
theorem IgnoredLambdaTrace.lam_succ (H : IgnoredLambdaTrace P n (.lam X y) (k+1)) :
    IgnoredLambdaTrace P (n+1) y k := by cases H with | lam H => exact H

/-- Application consumes one ignored control argument. -/
theorem IgnoredLambdaTrace.app_inv (H : IgnoredLambdaTrace P n (.app f a) k) :
    IgnoredLambdaTrace P n f (k+1) := by cases H with | app H => exact H

/-- Root beta substitutes only temporary controls and keeps the payload fixed. -/
theorem IgnoredLambdaTrace.beta_forward (H : IgnoredLambdaTrace P n (.app (.lam A b) a) k) :
    IgnoredLambdaTrace P n (b.inst a) k := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  simpa only [inst_eq_subst, Subst.liftN, Subst.one] using
    H.app_inv.lam_succ.subst (HT.cons (a := a))

/-- Constant expansion creates one control frame and one ignored argument. -/
theorem IgnoredLambdaTrace.constant_expansion (H : IgnoredLambdaTrace P n e k) :
    IgnoredLambdaTrace P n (constantExpansion e) k := .app (.lam H.lift)

/-- Opaque primitive heads cannot occur on a marked control path. -/
theorem IgnoredLambdaTrace.not_primitiveHead (H : IgnoredLambdaTrace P n e k) : ¬ PrimitiveHead e := by
  induction H with
  | payload | lam => exact id
  | app _ ih => exact ih

/-- The trace cannot end at a literal sort. -/
theorem IgnoredLambdaTrace.not_sort (H : IgnoredLambdaTrace P n (.sort u) k) : False := by cases H

/-- The trace cannot end at a literal Pi. -/
theorem IgnoredLambdaTrace.not_forallE (H : IgnoredLambdaTrace P n (.forallE A B) k) : False := by cases H

/-- The trace cannot end at a projection. -/
theorem IgnoredLambdaTrace.not_proj (H : IgnoredLambdaTrace P n (.proj s i e) k) : False := by cases H

/-- Two marked traces of identical syntax and arity select the same lower
payload, even through arbitrarily nested control applications and lambdas. -/
theorem IgnoredLambdaTrace.common_payload (H : IgnoredLambdaTrace P n e k)
    (K : IgnoredLambdaTrace Q n e k) : ∃ A b, P A b ∧ Q A b := by
  induction H with
  | @payload A b n HP =>
    obtain ⟨A', b', HQ, EA, Eb⟩ := K.lam_zero
    have HA := ProofShape.liftN_inj.1 EA
    have Hb := ProofShape.liftN_inj.1 Eb
    subst A' b'
    exact ⟨_, _, HP, HQ⟩
  | lam _ ih => exact ih K.lam_succ
  | app _ ih => exact ih K.app_inv

/-- Displayed eta preserves a positive pending control demand. A fresh variable
or proof marker is merely another ignored argument, so both eta forms work. -/
theorem IgnoredLambdaTrace.eta_iff (HE : EtaHead e f) :
    IgnoredLambdaTrace P n e (k+1) ↔ IgnoredLambdaTrace P n f (k+1) := by
  obtain ⟨A, arg, rfl, _⟩ := HE.shape
  exact ⟨fun H => H.lam_succ.app_inv.of_lift, fun H => .lam (.app H.lift)⟩

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Every stage-zero primitive preserves a marked ignored-argument trace.
Only constant expansion acts on its control path; other roots have incompatible
heads. Component computation is handled separately at payload lambdas. -/
theorem stage_zero_ignored_lambda_trace
    (R : ErasedStaticStructureEtaExpansionStage D 0 Δ e out)
    (H : IgnoredLambdaTrace P n e k) : IgnoredLambdaTrace P n out k := by
  rcases R with (R | R) | R
  · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
  · cases R with
    | sort => exact H.not_sort.elim
    | const => exact (H.not_primitiveHead trivial).elim
  · cases R; exact H.constant_expansion

/-- Compatible computation preserves the pending ignored-argument count and
lower payload histories. Actual endpoint typing justifies descent of payload
components below temporary binders; no argument observation is required. -/
theorem proofErase_scoped_compute_ignoredLambdaTrace
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ e out n k}, Step Δ e out → IgnoredLambdaTrace P n e k → IgnoredLambdaTrace P n out k)
    (hpayload : LambdaOriginComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (H : IgnoredLambdaTrace P n source k) : IgnoredLambdaTrace P n out k := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n k e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE (ih₁ hΓ' W ht EΓ Ee H)
  | app RF RX ihf _ =>
    obtain ⟨f, x, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ'
    exact .app (ihf hΓ' W hf EΓ Ef H.app_inv)
  | proj => exact H.not_proj.elim
  | lam RA RB ihA ihb =>
    cases k with
    | zero =>
      obtain ⟨A, b, HP, rfl, rfl⟩ := H.lam_zero
      obtain ⟨A', b', HP', EX, EY⟩ := hpayload hΓ' W HP (EΓ ▸ RA) (EΓ ▸ RB)
      rw [EX, EY]
      exact IgnoredLambdaTrace.payload HP'
    | succ k =>
      obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact .lam (ihb hΓA W' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb H.lam_succ)
  | forallE => exact H.not_forallE.elim

/-- A computed original lambda retains an ignored-control trace with its exact
stage-zero histories and no pending arguments. Comparison may inspect the
function position by increasing the pending count without losing the payload. -/
theorem proofErase_stage_zero_lambda_trace
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hn : ¬ IsProof Γ (.lam C a))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) out) :
    IgnoredLambdaTrace (StageZeroLambdaOrigin D Γ C a u) 0 out 0 := by
  apply proofErase_scoped_compute_ignoredLambdaTrace
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) stage_zero_ignored_lambda_trace
    (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero [])
    (HasType.lam hC ha) rfl (show proofErase Γ (.lam C a) = .lam _ _ from if_neg hn)
  simpa only [ProofShape.liftN_zero] using
    (IgnoredLambdaTrace.payload (n := 0) (StageZeroLambdaOrigin.refl hC ha))

end Lean4Lean.VEnv.Strengthening
