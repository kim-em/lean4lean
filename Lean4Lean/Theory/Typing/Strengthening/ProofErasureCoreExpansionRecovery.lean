import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreExpansionConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeSubstitution

/-! # Native recovery modulo ordinary core reduction

A source relation whose typed paths have core common reducts does not require
exact target replay. Every native certificate can be recovered in the repaired
ordinary core after reducing its selected output. This applies to mixed core
and controlled beta expansion without purity assumptions.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private forall_parts projection_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]

/-- Native recovery transfers to the ordinary core when each source conversion
has a core common reduct. The selected result computes forward to the new native
output, rather than requiring exact recovery at its original syntax. -/
theorem recovery_of_compute_join (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (Step hq) (proofErase Γ e) out)
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) Δ source out' ∧ Compute (Step hq) out out' := by
  induction R generalizing Γ e T with
  | bvar => exact ⟨_, .bvar, .refl⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) EB
    exact ⟨_, .lam HR, .forallE .refl RC⟩
  | app R ih =>
    obtain ⟨f, x, rfl, _, EF, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih hΓ hf EΓ EF
    obtain ⟨A', B', rfl, _, RB⟩ := forall_parts hq RC
    refine ⟨_, .app HR, ?_⟩
    simpa only [ProofShape.inst_eq_subst] using RB.subst (fun H => erased_iota_primitive_subst H)
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, CA⟩ := ihA hΓ hA EΓ EA
    have EoutA := (CA.scoped (Δ := Δ) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outA
    obtain ⟨outB, HB, CB⟩ := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB
    have EoutB := (CB.scoped (Δ := Δ) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outB
    exact ⟨_, .forallE HA HB, .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih hΓ hm.hasType.2 EΓ EM
    have RC' := RC.scoped (Δ := Δ) (Step' := fun _ => Step hq) (fun H => .base H)
    obtain ⟨args', rfl, Hargs⟩ := RC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    refine ⟨_, .proj hi HT hj (Hargs.length_eq.symm.trans hlen) HR, ?_⟩
    exact projection_compute hq (Hargs.imp (fun _ _ H => forget_scope H))
  | convert R RC ih =>
    obtain ⟨out', HR, HC⟩ := ih hΓ ht EΓ Ee
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := heA.isType henv hΓ
    have RC' := RC
    rw [← EΓ, ← EA] at RC'
    obtain ⟨shared, Hold, Hout⟩ := hjoin hΓ hA RC'
    obtain ⟨final, Hnative, Hshared⟩ := confluent hq hcon hΓ hA (EA ▸ HC) Hold
    exact ⟨final, HR.convert (Hnative.scoped (fun H => .base H)), Hout.trans Hshared⟩

/-- Ordinary computation interleaved with controlled expansions can be removed
from native recovery after computing the selected type further. The image and
its context may contain arbitrary constants, projections and dependent binders. -/
theorem expansion_recovery (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out' ∧
      Compute (Step hq) out out' :=
  recovery_of_compute_join hq hcon (erased_core_expansion_descent (sound hq) hr)
    (fun hΓ ht R => proofErase_core_expansion_join (sound hq) hr
      (typed_core_confluence hq hcon) hΓ ht R) R hΓ ht rfl rfl

/-- A mixed native output merely joined to the assigned type suffices to
recover a common core reduct of that assigned type. Neither join branch is
required to be empty. -/
theorem expansion_recovery_align (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) native)
    (HJ : ComputeJoin (Step hq) (proofErase Γ T) native) :
    ∃ out, ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out ∧
      Compute (Step hq) (proofErase Γ T) out := by
  obtain ⟨core, RN, RC⟩ := expansion_recovery hq hcon hr hΓ ht R
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_core_expansion_descent (sound hq) hr) hΓ ht R
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  obtain ⟨shared, RT, RS⟩ := HJ
  obtain ⟨out, Rcore, Rshared⟩ := confluent hq hcon hΓ hA (EA ▸ RC) (EA ▸ RS)
  exact ⟨out, RN.convert (Rcore.scoped (fun H => .base H)), RT.trans Rshared⟩

/-- Joined native images suffice for substitution of mixed-expansion recovery
on arbitrary typed sources. Both stages retain directed core reductions of the
selected output, so they compose without exact assigned-type recovery. -/
theorem expansion_recovery_joined_subst (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (HI : JoinedNative.Images hq Γ Γ₀ τ)
    (R : ScopedTypeRecovery (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) out' ∧ Compute (Step hq) (out.subst τ) out' := by
  obtain ⟨native, RN, RC⟩ := expansion_recovery hq hcon hr W.wf ht R
  obtain ⟨out', RN', RC'⟩ := JoinedNative.recovery_subst hcon RN hΓ₀ W ES ht rfl rfl HI
  rw [← proofErase_subst_with hΓ₀ W ht ES] at RN'
  exact ⟨out', RN', (RC.subst (fun H => erased_iota_primitive_subst H)).trans RC'⟩

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore
