import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Composite recovery under computation of context oracles

For the repaired ordinary core, pointwise oracle computation preserves every
source-typed recovery, allowing its selected output to compute further. The
conversion case uses typed confluence, and projection follows computation of
the actual erased field recipe. No joint-stage confluence is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
namespace ErasedQuotCore

private theorem forall_parts (hq : QuotRegistered env)
    (R : Compute (Step hq) (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute (Step hq) A A' ∧ Compute (Step hq) B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (E ▸ erased_iota_primitive_head H).elim
  | beta H =>
    cases E
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts H
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA, HB⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA', HB'⟩ := ih₂ rfl
    exact ⟨_, _, HE, HA.trans HA', HB.trans HB'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | app | proj | lam => cases E

private theorem oracle_cons (hq : QuotRegistered env)
    (H : ∀ i, Compute (Step hq) (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, Compute (Step hq) (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (fun H => erased_iota_primitive_liftN H)

private theorem instOuter_compute (hq : QuotRegistered env)
    (H : List.Forall₂ (Compute (Step hq)) args args') (body : ProofShape) :
    Compute (Step hq) (body.instOuter args) (body.instOuter args') := by
  apply Compute.subst_images (fun H => erased_iota_primitive_liftN H)
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < args.length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

private theorem projection_compute (hq : QuotRegistered env)
    (H : List.Forall₂ (Compute (Step hq)) args args') :
    Compute (Step hq) (projectionType s info doms j hj args m)
      (projectionType s info doms j hj args' m) := by
  apply instOuter_compute
  exact (Lean4Lean.List.forall₂_take H info.nparams).append'
    (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))

private theorem recovery_oracle_reduce_aux
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ScopedTypeRecovery (fun _ => Step hq) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HO : ∀ i, Compute (Step hq) (contextOracle Δ i) (contextOracle Δ' i)) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) Δ' source out' ∧ Compute (Step hq) out out' := by
  induction R generalizing Γ e T Δ' with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨out', HR, HC⟩ := ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (oracle_cons hq HO)
    exact ⟨_, .lam HR, .forallE .refl HC⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HC⟩ := ih hΓ hf EΓ Ef HO
    obtain ⟨A', B', rfl, _, HB⟩ := forall_parts hq HC
    refine ⟨_, .app HR, ?_⟩
    simpa only [ProofShape.inst_eq_subst] using HB.subst (fun H => erased_iota_primitive_subst H)
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, CA⟩ := ihA hΓ hA EΓ EA HO
    have EoutA := (CA.scoped (Δ := Δ') (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outA
    obtain ⟨outB, HB, CB⟩ := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB (oracle_cons hq HO)
    have EoutB := (CB.scoped (Δ := Δ') (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outB
    exact ⟨_, .forallE HA HB, .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HC⟩ := ih hΓ hm.hasType.2 EΓ Em HO
    have HC' := HC.scoped (Δ := Δ') (Step' := fun _ => Step hq) (fun H => .base H)
    obtain ⟨args', rfl, Hargs⟩ := HC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    refine ⟨_, .proj hi HT hj (Hargs.length_eq.symm.trans hlen) HR, ?_⟩
    exact projection_compute hq (Hargs.imp (fun _ _ H => forget_scope H))
  | convert R RC ih =>
    obtain ⟨out', HR, HC⟩ := ih hΓ ht EΓ Ee HO
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
      (ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))) hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    obtain ⟨shared, Hnew, Hold⟩ := confluent hq hcon hΓ hA
      (EA ▸ HC) (EA ▸ forget_scope RC)
    exact ⟨shared, HR.convert (Hnew.scoped (fun H => .base H)), Hold⟩

/-- Every source-typed recovery in the repaired ordinary core survives
pointwise computation of its context oracle. The expression stays fixed and
the old selected output computes to the new one. Target oracle entries need
no separate typing premise; this is a raw recovery certificate theorem. -/
theorem recovery_oracle_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx Γ) i) (contextOracle Δ' i))
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) Δ' (proofErase Γ e) out' ∧
      Compute (Step hq) out out' :=
  recovery_oracle_reduce_aux hq hcon R hΓ ht rfl rfl HO

/-- Reducing a typed binder annotation preserves recovery for every typed
body, including composite applications and projections. The output may reduce
further, and the recovered expression is erased in the actual new context. -/
theorem recovery_domain_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx (B :: Γ))
        (proofErase (B :: Γ) e) out' ∧
      ScopedCompute (fun _ => Step hq) (proofEraseCtx (B :: Γ)) out out' := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (forget_scope RA).liftN (fun H => erased_iota_primitive_liftN H)
    | succ i => exact .refl
  obtain ⟨out', HR, HC⟩ := recovery_oracle_reduce hq hcon hΓA he HO R
  have Hcompare : JointCompare (fun _ => Step hq) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ B) := .compute RA .refl (.leaf .refl)
  have HAB := (proofErase_joint_compare_reflect
    (ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq)))
    hΓ hA hB Hcompare).2 rfl (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hB)
  have W := IsDefEqCtx.succ .zero (HAB.of_l henv hΓ hA)
  rw [proofErase_defeqCtx hΓA W he] at HR
  exact ⟨out', HR, HC.scoped (fun H => .base H)⟩

/-- A recovered Pi survives pointwise oracle reduction for any typed expression.
Both its domain and codomain have explicit computation paths to their new
choices; no argument-guard conversion is asserted. -/
theorem recovery_pi_oracle_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx Γ) i) (contextOracle Δ' i))
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e)
      (.forallE A B)) :
    ∃ A' B', ScopedTypeRecovery (fun _ => Step hq) Δ' (proofErase Γ e) (.forallE A' B') ∧
      Compute (Step hq) A A' ∧ Compute (Step hq) B B' := by
  obtain ⟨out', HR, HC⟩ := recovery_oracle_reduce hq hcon hΓ ht HO R
  obtain ⟨A', B', rfl, HA, HB⟩ := forall_parts hq HC
  exact ⟨A', B', HR, HA, HB⟩

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
