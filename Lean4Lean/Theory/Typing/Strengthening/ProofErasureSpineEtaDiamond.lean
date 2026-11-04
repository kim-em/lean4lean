import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstantEtaDiamond

/-! # Eta diamonds for arbitrary typed variable/constant application spines

Native type uniqueness up to a core join extends through every application.
Pi inversion joins the dependent codomains; raw core substitution instantiates
the common codomain at the unchanged argument. Argument native evidence is
unnecessary. Typed replay then composes both outer conversion histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- A variable or named constant followed by any number of applications.
Arguments are unrestricted raw expressions; this is not a purity predicate. -/
inductive ProofShape.NativeEtaSpine : ProofShape → Prop where
  | bvar : NativeEtaSpine (.bvar i)
  | const : NativeEtaSpine (.const c ls)
  | app : NativeEtaSpine f → NativeEtaSpine (.app f a)

variable [Params]
/-- Application recovery selects a native function Pi and then computes
from its exact codomain instantiation. Arguments are not recovered. -/
theorem ProofShape.ScopedTypeRecovery.app_origin
    (R : ScopedTypeRecovery Step Δ (.app f a) out) :
    ∃ A B, ScopedTypeRecovery Step Δ f (.forallE A B) ∧ ScopedCompute Step Δ (B.inst a) out := by
  generalize E : ProofShape.app f a = e at R
  induction R with
  | app R => cases E; exact ⟨_, _, R, .refl⟩
  | convert _ RC ih =>
    obtain ⟨A, B, R, RP⟩ := ih E
    exact ⟨A, B, R, RP.trans RC⟩
  | bvar | sort | const | lam | forallE | proj => cases E

/-- Any two native outputs of a typed application spine are core-joined
when each guard relation has core-joinable typed paths. No native certificates
are needed for the spine's arguments, including dependent and proof arguments. -/
theorem proofErase_spine_native_core_join
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hc : TypedCoreConfluence Core) (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hsubst : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (H : NativeEtaSpine source)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = source)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) source A)
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) source B) : ComputeJoin Core A B := by
  induction H generalizing e T A B with
  | bvar =>
    obtain rfl := erase_bvar_inv Ee
    exact proofErase_variable_native_core_join hc hlj hrj hΓ he RL RR
  | @const c ls =>
    obtain rfl := erase_const_inv Ee
    have hn : ¬ IsProof Γ (.const c ls) := by intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    exact proofErase_constant_native_core_join hld hc hlj hrj hΓ he hn RL RR
  | @app f a H ih =>
    obtain ⟨f₀, a₀, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := he.app_inv henv hΓ
    obtain ⟨XL, YL, RFL, RCL⟩ := RL.app_origin
    obtain ⟨XR, YR, RFR, RCR⟩ := RR.app_origin
    obtain ⟨shared, HL, HR⟩ := ih hf Ef RFL RFR
    obtain ⟨X, Y, rfl, _, HYL⟩ := HL.pi_parts hpi
    obtain ⟨X', Y', E, _, HYR⟩ := HR.pi_parts hpi
    cases E
    have HB : ComputeJoin Core (YL.inst a) (YR.inst a) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        (ComputeJoin.subst hsubst (σ := ProofShape.Subst.one a) ⟨_, HYL, HYR⟩)
    obtain ⟨CL, htL, EL⟩ := proofErase_scoped_typeRecovery_replay hld hΓ he
      (Ee ▸ ScopedTypeRecovery.app RFL)
    obtain ⟨CR, htR, ER⟩ := proofErase_scoped_typeRecovery_replay hrd hΓ he
      (Ee ▸ ScopedTypeRecovery.app RFR)
    obtain ⟨_, hCL⟩ := htL.isType henv hΓ
    obtain ⟨_, hCR⟩ := htR.isType henv hΓ
    rw [← EL, ← ER] at HB
    have JL := hlj hΓ hCL (EL ▸ RCL)
    have JR := hrj hΓ hCR (ER ▸ RCR)
    exact (JL.symm.trans_typed hc hΓ hCL HB).trans_typed hc hΓ hCR JR

/-- Two native eta expansions of any retained variable/constant application
spine have a core common reduct when the native guards satisfy the stated
typed core-join laws. This includes non-normalizing and impure arguments. -/
theorem proofErase_spine_native_eta_diamond
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hc : TypedCoreConfluence Core) (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hsubst : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (H : NativeEtaSpine (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion Left (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion Right (proofEraseCtx Γ) (proofErase Γ e) b) : ComputeJoin Core a b := by
  cases RL with
  | intro RN SN =>
    cases RR with
    | intro RN' SN' =>
      exact proofErase_native_eta_type_diamond hld hrd hpi hΓ he RN RN' SN SN'
        (proofErase_spine_native_core_join hld hrd hc hpi hsubst hlj hrj H hΓ he rfl RN RN')

end Lean4Lean.VEnv.Strengthening
