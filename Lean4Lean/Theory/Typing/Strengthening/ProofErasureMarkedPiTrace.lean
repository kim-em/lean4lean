import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroPiReadout

/-! # Marked Pi traces with pending ignored control arguments

The pending argument count distinguishes a payload Pi from a generated
control lambda. No variable or argument observation is used along the control
path. Payloads retain their lower component histories below temporary binders.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open PiOriginObservation (FixedTail)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- A marked Pi is observed after consuming exactly the pending control
arguments. Payload depth counts temporary binders above its original context. -/
inductive MarkedPiTrace (P : ProofShape → ProofShape → Prop) : Nat → ProofShape → Nat → Prop where
  | payload : P A b → MarkedPiTrace P n ((ProofShape.forallE A b).liftN n) 0
  | lam : MarkedPiTrace P (n+1) b k → MarkedPiTrace P n (.lam A b) (k+1)
  | app : MarkedPiTrace P n f (k+1) → MarkedPiTrace P n (.app f a) k

/-- Substitution of temporary controls fixes every marked lower payload. -/
theorem MarkedPiTrace.subst (H : MarkedPiTrace P n e k) (HT : FixedTail n m σ) :
    MarkedPiTrace P m (e.subst σ) k := by
  induction H generalizing m σ with
  | payload h => rw [HT.payload]; exact .payload h
  | lam _ ih => exact .lam (ih HT.lift)
  | app _ ih => exact .app (ih HT)

/-- Inserting a temporary binder lifts syntax and payload depth together. -/
theorem MarkedPiTrace.lift (H : MarkedPiTrace P n e k) :
    MarkedPiTrace P (n+1) (e.liftN 1) k := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ H.subst HT

/-- A lifted control path can be read below its fresh unused binder. -/
theorem MarkedPiTrace.of_lift (H : MarkedPiTrace P (n+1) (e.liftN 1) k) :
    MarkedPiTrace P n e k := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  have R := H.subst (HT.cons (a := .proof))
  simpa only [lift_subst_cons, subst_id] using R

/-- A literal Pi is exactly a marked payload with no pending arguments. -/
theorem MarkedPiTrace.pi_inv (H : MarkedPiTrace P n (.forallE X y) k) :
    k = 0 ∧ ∃ A b, P A b ∧ X = A.liftN n ∧ y = b.liftN n 1 := by
  cases H with
  | payload HP => exact ⟨rfl, _, _, HP, rfl, rfl⟩

/-- A zero-arity marked Pi trace cannot be a control lambda. -/
theorem MarkedPiTrace.not_lam_zero (H : MarkedPiTrace P n (.lam X y) 0) : False := by cases H

/-- A literal lambda at positive pending arity is a control frame. -/
theorem MarkedPiTrace.lam_succ (H : MarkedPiTrace P n (.lam X y) (k+1)) :
    MarkedPiTrace P (n+1) y k := by cases H with | lam H => exact H

/-- Application consumes one ignored control argument. -/
theorem MarkedPiTrace.app_inv (H : MarkedPiTrace P n (.app f a) k) :
    MarkedPiTrace P n f (k+1) := by cases H with | app H => exact H

/-- Root beta substitutes only temporary controls and keeps the payload fixed. -/
theorem MarkedPiTrace.beta_forward (H : MarkedPiTrace P n (.app (.lam A b) a) k) :
    MarkedPiTrace P n (b.inst a) k := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  simpa only [inst_eq_subst, Subst.liftN, Subst.one] using
    H.app_inv.lam_succ.subst (HT.cons (a := a))

/-- Constant expansion creates one control frame and one ignored argument. -/
theorem MarkedPiTrace.constant_expansion (H : MarkedPiTrace P n e k) :
    MarkedPiTrace P n (constantExpansion e) k := .app (.lam H.lift)

/-- Opaque primitive heads cannot occur on a marked control path. -/
theorem MarkedPiTrace.not_primitiveHead (H : MarkedPiTrace P n e k) : ¬ PrimitiveHead e := by
  induction H with
  | payload | lam => exact id
  | app _ ih => exact ih

/-- The trace cannot end at a literal sort. -/
theorem MarkedPiTrace.not_sort (H : MarkedPiTrace P n (.sort u) k) : False := by cases H

/-- The trace cannot end at a projection. -/
theorem MarkedPiTrace.not_proj (H : MarkedPiTrace P n (.proj s i e) k) : False := by cases H

/-- Two marked traces of identical syntax and arity select the same lower
payload, even through arbitrarily nested control applications and lambdas. -/
theorem MarkedPiTrace.common_payload (H : MarkedPiTrace P n e k)
    (K : MarkedPiTrace Q n e k) : ∃ A b, P A b ∧ Q A b := by
  induction H with
  | @payload A b n HP =>
    obtain ⟨_, A', b', HQ, EA, Eb⟩ := K.pi_inv
    have HA := ProofShape.liftN_inj.1 EA
    have Hb := ProofShape.liftN_inj.1 Eb
    subst A' b'
    exact ⟨_, _, HP, HQ⟩
  | lam _ ih => exact ih K.lam_succ
  | app _ ih => exact ih K.app_inv

/-- Displayed eta preserves a positive pending control demand. A fresh variable
or proof marker is merely another ignored argument, so both eta forms work. -/
theorem MarkedPiTrace.eta_iff (HE : EtaHead e f) :
    MarkedPiTrace P n e (k+1) ↔ MarkedPiTrace P n f (k+1) := by
  obtain ⟨A, arg, rfl, _⟩ := HE.shape
  exact ⟨fun H => H.lam_succ.app_inv.of_lift, fun H => .lam (.app H.lift)⟩

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Every stage-zero primitive preserves a marked ignored-argument trace.
Only constant expansion acts on its control path; other roots have incompatible
heads. Component computation is handled separately at payload Pis. -/
theorem stage_zero_marked_pi_trace
    (R : ErasedStaticStructureEtaExpansionStage D 0 Δ e out)
    (H : MarkedPiTrace P n e k) : MarkedPiTrace P n out k := by
  rcases R with (R | R) | R
  · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
  · cases R with
    | sort => exact H.not_sort.elim
    | const => exact (H.not_primitiveHead trivial).elim
  · cases R; exact H.constant_expansion

/-- Compatible computation preserves the pending ignored-argument count and
lower payload histories. Actual endpoint typing justifies descent of payload
components below temporary binders; no argument observation is required. -/
theorem proofErase_scoped_compute_markedPiTrace
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ e out n k}, Step Δ e out → MarkedPiTrace P n e k → MarkedPiTrace P n out k)
    (hpayload : PiOriginComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (H : MarkedPiTrace P n source k) : MarkedPiTrace P n out k := by
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
    cases H with
    | lam H =>
      obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact .lam (ihb hΓA W' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb H)
  | forallE RA RB ihA ihb =>
    obtain ⟨rfl, A, b, HP, rfl, rfl⟩ := H.pi_inv
    obtain ⟨A', b', HP', EX, EY⟩ := hpayload hΓ' W HP (EΓ ▸ RA) (EΓ ▸ RB)
    rw [EX, EY]
    exact MarkedPiTrace.payload HP'

/-- A computed original Pi retains exact stage-zero component histories and
an ignored-control trace with no pending arguments. -/
theorem proofErase_stage_zero_pi_trace
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    MarkedPiTrace (StageZeroPiOrigin D Γ A B u v) 0 out 0 := by
  have hPi := HasType.forallE hA hB
  apply proofErase_scoped_compute_markedPiTrace
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) stage_zero_marked_pi_trace
    (stage_zero_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero [])
    hPi rfl (show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi))
  simpa only [ProofShape.liftN_zero] using
    (MarkedPiTrace.payload (n := 0) (StageZeroPiOrigin.refl hA hB))

end Lean4Lean.VEnv.Strengthening
