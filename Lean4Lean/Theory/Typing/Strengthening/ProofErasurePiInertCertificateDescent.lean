import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCertificateDescent

/-! # Exact certificate descent for the Pi-inert outer skeleton

The outer source-head restriction descends with each primitive. Guards still
use the full stage: their existing exact certificate descent is sufficient to
reconstruct the restricted lower root. Thus removing unused binders preserves
both the numerical stage and the restricted outer computation relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Binder insertion preserves the primitive-head test exactly. -/
theorem ProofShape.primitiveHead_liftN_iff : PrimitiveHead (a.liftN n k) ↔ PrimitiveHead a := by
  induction a generalizing k <;> simp_all [ProofShape.liftN, PrimitiveHead]

/-- The admitted outer heads reflect through binder insertion. -/
theorem ProofShape.pi_inert_head_liftN
    (H : PrimitiveHead (a.liftN n k) ∨ ∃ u, a.liftN n k = .sort u) :
    PrimitiveHead a ∨ ∃ u, a = .sort u := by
  rcases H with H | ⟨u, H⟩
  · exact .inl (primitiveHead_liftN_iff.1 H)
  · exact .inr ⟨u, ProofShape.liftN_inj.1 (show a.liftN n k = (ProofShape.sort u).liftN n k from H)⟩

variable [Params]
/-- Every Pi-inert root descends to a lower Pi-inert computation at the same
stage. Native recovery and singleton guards descend in the full earlier stage;
the source-head evidence is retained separately for the reconstructed root. -/
theorem pi_inert_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent (PiInertStage D stage) (PiInertStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    obtain ⟨H, HH⟩ := H
    have Hhead := ProofShape.pi_inert_head_liftN HH
    rcases H with (H | H) | H
    · obtain ⟨e', HE, R, E⟩ := erased_joint_zero_certificate_descent hs hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => ⟨.inl (.inl H), .inl (erased_iota_primitive_head H)⟩), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_level_primitive_certificate_descent hΓ hΓ' W ht H
      refine ⟨e', HE, R.mono (fun H => ⟨.inl (.inr H), ?_⟩), E⟩
      cases H with
      | sort => exact .inr ⟨_, rfl⟩
      | const => exact .inl trivial
    · cases H with
      | intro hn =>
        have hne : ¬ IsProof Γ e := by
          intro hp
          exact hn (by rw [proofErase_eq_proof.2 hp]; rfl)
        refine ⟨_, (constantExpansion_equal ht).symm, ?_, ?_⟩
        · rw [proofErase_constantExpansion hΓ ht hne]
          exact .base ⟨.inr (.intro (fun H => hne (proofErase_eq_proof.1 H))), Hhead⟩
        · rw [proofErase_constantExpansion hΓ ht hne, constantExpansion_liftN]
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    obtain ⟨H, HH⟩ := H
    have Hhead := ProofShape.pi_inert_head_liftN HH
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D stage) (ErasedStaticStructureEtaExpansionStage D stage) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage
    rcases H with H | H | H | H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht ⟨H, HH⟩
      exact ⟨e', HE, R.mono (fun H => ⟨.inl H.1, H.2⟩), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_carrier_recovered_singleton_certificate_descent heq hd hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => ⟨.inr (.inl H), .inl H.2.head⟩), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_computed_joint_prefix_certificate_descent heq hd hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => ⟨.inr (.inr (.inl H)), .inl H.head⟩), E⟩
    · cases H with
      | intro R =>
        obtain ⟨A, he, RA, EA⟩ := proofErase_scoped_recovery_certificate_descend hd hΓ hΓ' W ht rfl R
        have hn : ¬ IsProof Γ e := fun hp => RA.ne_proof (proofErase_eq_proof.2 hp)
        refine ⟨_, (nativeIdentityExpansion_equal he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
        · rw [proofErase_nativeIdentityExpansion hΓ he hn]
          exact .base ⟨.inr (.inr (.inr (.inl (.intro RA)))), Hhead⟩
        · rw [proofErase_nativeIdentityExpansion hΓ he hn]
          simp only [ProofShape.liftN, EA, liftVar, Nat.zero_lt_succ, ↓reduceIte]
    · cases H with
      | intro R S =>
        obtain ⟨A, B, he, RN, EA, _⟩ := proofErase_recovered_pi_certificate_descend hd hΓ hΓ' W ht R
        obtain ⟨_, hPi⟩ := he.isType henv hΓ
        obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
        have hA := (EA ▸ S).descend hΓ hΓ' W hA
        have hn : ¬ IsProof Γ e := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
        refine ⟨_, (IsDefEq.eta he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
        · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
          exact .base ⟨.inr (.inr (.inr (.inr (.inl (.intro RN (DomainSort.of_typed hΓ hA)))))), Hhead⟩
        · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
          simp only [ProofShape.liftN, etaArgument_liftN, EA]
          rw [ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)]
    · cases H with
      | intro hi hx ha hp RN =>
        rename_i family info ls rawPs
        obtain ⟨A, heA, RL, EA⟩ := proofErase_scoped_recovery_certificate_descend hd hΓ hΓ' W ht rfl RN
        obtain ⟨rawPs, Es, Eps⟩ := ProofShape.liftN_const_spine_inv EA
        obtain ⟨ps, rfl, rfl⟩ := proofErase_const_spine_inv Es
        have hps : ps.length = info.nparams := by
          have H := congrArg List.length Eps
          simp only [List.length_map] at H
          omega
        have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hps hx heA).2 ha
        have HE := (IsDefEq.structEta hi hps hx heA hc).symm
        have hn : ¬ IsProof Γ e := fun H => RL.ne_proof (proofErase_eq_proof.2 H)
        have hnc : ¬ IsProof Γ (structExpand family info ls ps e) :=
          fun H => hn ((isProof_congr hΓ HE).2 H)
        refine ⟨structExpand family info ls ps e, HE.toU.of_l henv hΓ ht, ?_, ?_⟩
        · rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc]
          exact .base ⟨.inr (.inr (.inr (.inr (.inr
            (.intro hi hx ha (by simpa only [List.length_map] using hps)
              (by simpa only [Es] using RL)))))), Hhead⟩
        · rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc, nativeStructureOutput_liftN, ← Eps]

/-- Typed Pi-inert computation reflects and lifts through any unused binder
block, retaining the exact raw endpoints and the same restricted stage. -/
theorem proofErase_pi_inert_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN count offset) (out.liftN count offset) ↔
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (pi_inert_stage_certificate_descent heq hs n) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (pi_inert_stage_rename heq hs n) (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
