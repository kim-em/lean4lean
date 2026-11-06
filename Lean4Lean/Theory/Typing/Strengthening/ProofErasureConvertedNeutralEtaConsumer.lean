import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedNeutralEtaChecking

/-! # Neutral eta consumers with independently recovered domains

The assigned function type and native recovered Pi may have different domains.
Retained comparisons from every computed assigned-domain annotation to the
selected native domain supply residual readout. This is a local induction
interface, not a claim of semantic conversion completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Independent full core residuals of every typed neutral eta consumer
compare at one fixed stage. Native Pi recovery remains explicit; the paths
include recursive delta, projection, quotient, stored iota and universe steps. -/
theorem proofErase_neutral_eta_consumer_core_of_domain_check
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (.bvar i) (.forallE nativeA rawB))
    (SC : DomainSort (proofEraseCtx Γ) nativeA u)
    (Hdomain : ∀ {C}, Compute (ErasedLevelCore D) (proofErase Γ A) C →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
        (proofEraseCtx Γ) false C nativeA)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  have V : NeutralEtaVariant (fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) 0
      (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.bvar i))) :=
    (proofErase_neutral_eta_consumer_variant hΓ hA hf hn hu ht).guard_mono
      (fun H => ⟨H.1, .beta H.2⟩)
  obtain ⟨left', right', PL, PR, V⟩ := neutral_eta_level_core_residuals hc
    (fun H R => ⟨H.1, H.2.trans R⟩) hΓ (ht.instN henv Ctx.InstN.zero hf) V RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans PL).scoped (fun H => .base H))
  have HG {C j mode} (H : j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) :
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1)) (proofEraseCtx Γ) mode
        (.lam C (.app (.bvar (j+1)) (.bvar 0))) (.bvar j) := by
    obtain ⟨rfl, R⟩ := H
    simpa only [etaArgument, if_neg hu] using
      (native_eta_converted_domain_check (mode := mode) RN SC (Hdomain R))
  have HC := neutral_eta_variant_guarded_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1)) (fun H => HG H)
    V hΓ HE.hasType.2 EE ContextRenaming.identity
  exact .compute PL.in_static_stage PR.in_static_stage HC

/-- Every pair of independent full ordinary-core residuals of a proof-domain
neutral eta consumer compares. Both simulation directions retain actual source
typing; no raw confluence or arbitrary proof-marker substitution is assumed. -/
theorem proofErase_proof_neutral_eta_consumer_core_of_domain_check
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort .zero))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (.bvar i) (.forallE nativeA rawB))
    (SC : DomainSort (proofEraseCtx Γ) nativeA .zero)
    (Hdomain : ∀ {C}, Compute (ErasedLevelCore D) (proofErase Γ A) C →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
        (proofEraseCtx Γ) false C nativeA)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  let Guard := fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C
  have hsort {C j} (H : Guard C j) : DomainSort (proofEraseCtx Γ) C .zero := by
    obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hA rfl rfl (H.2.scoped (fun H => .base H))
    exact EE ▸ DomainSort.of_typed hΓ HE.hasType.2
  have hg {C j C'} (H : Guard C j) (R : Compute (ErasedLevelCore D) C C') : Guard C' j :=
    ⟨H.1, H.2.trans R⟩
  have V := proofErase_proof_neutral_eta_consumer_variant (D := D) hΓ hA hf hn ht
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  have hright := ht.instN henv Ctx.InstN.zero hf
  obtain ⟨b₁, RB₁, V₁⟩ := proof_neutral_eta_core_left hs
    (Guard := Guard) (fun H R => hg H R) (fun H => hsort H) RL V hΓ hleft rfl ContextRenaming.identity
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ hright RR RB₁
  obtain ⟨eb, HB, EB⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hright rfl rfl (RB₁.scoped (fun H => .base H))
  obtain ⟨p', RP, V₂⟩ := proof_neutral_eta_core_left hs
    (Guard := Guard) (fun H R => hg H R) (fun H => hsort H) RB₁' V₁.symm
    hΓ HB.hasType.2 EB ContextRenaming.identity
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans RP).scoped (fun H => .base H))
  have HG {C j mode} (H : Guard C j) :
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1)) (proofEraseCtx Γ) mode
        (.lam C (.app (.bvar (j+1)) .proof)) (.bvar j) := by
    obtain ⟨rfl, R⟩ := H
    simpa only [etaArgument, if_pos (show VLevel.zero ≈ VLevel.zero from rfl)] using
      (native_eta_converted_domain_check (mode := mode) RN SC (Hdomain R))
  have HC := proof_neutral_eta_variant_guarded_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1)) (fun H => HG H)
    V₂.symm hΓ HE.hasType.2 EE ContextRenaming.identity
  exact .compute RP.in_static_stage RQ.in_static_stage HC

/-- A constructive finite staged certificate aligns the assigned and declared
Pi domains. Lookup supplies native recovery at the declared domain, and its
expansion is checked against the assigned-domain eta wrapper at stage n+1.
No native recovery at the converted domain is postulated. -/
theorem staged_converted_lookup_eta_consumer_core
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (HL : Lookup Γ i (.forallE C E)) (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HA : LevelStagedCastGuard D stage false (proofErase Γ A) (proofErase Γ C))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  by_cases hp : IsProof Γ (.bvar i)
  · have hη := IsDefEq.eta hf
    have EE : proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))) =
        proofErase Γ (t.inst (.bvar i)) := by
      have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
      rw [proofErase_instN hΓF hη.hasType.1 Ctx.InstN.zero ht,
        proofErase_instN hΓF hf Ctx.InstN.zero ht,
        proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ hη).2 hp)]
    obtain ⟨out, RP, RQ⟩ := hc hΓ (ht.instN henv Ctx.InstN.zero hf) (EE ▸ RL) RR
    exact .compute RP.in_static_stage RQ.in_static_stage (.leaf .refl)
  have hfC : env.HasType univs Γ (.bvar i) (.forallE C E) := .bvar HL
  obtain ⟨_, hPi⟩ := hfC.isType henv hΓ
  have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hp
  have EP : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C :: Γ) E) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D stage) hΓ HL hp .refl
  rw [EF, EP] at RN
  have HD {out} (R : Compute (ErasedLevelCore D) (proofErase Γ A) out) :
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
        (proofEraseCtx Γ) false out (proofErase Γ C) :=
    (HA.forward heq hs hl hcon hc hreg hoff hD R .refl).mono
      (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_succ stage) H)
  by_cases hu : u ≈ .zero
  · have hA0 := (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA
    have hC0 := (IsDefEq.sortDF (hC.sort_r henv hΓ) (by trivial) hu).defeq hC
    exact proofErase_proof_neutral_eta_consumer_core_of_domain_check
      heq hs hc hΓ hA0 hf hp ht RN (.of_typed hΓ hC0) (fun R => HD R) RL RR
  · exact proofErase_neutral_eta_consumer_core_of_domain_check
      heq hs hc hΓ hA hf hp hu ht RN (.of_typed hΓ hC) (fun R => HD R) RL RR

omit [Params] in
/-- Actual environments discharge the primitive interfaces. The retained
finite domain certificate supports converted-domain eta at every sort and
through arbitrary independent ordinary-core tails. -/
theorem EnvironmentCore.staged_converted_lookup_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {stage mode Γ u A B C E i t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      Lookup Γ i (.forallE C E) → env.HasType U Γ (.bvar i) (.forallE A B) →
      env.HasType U (.forallE A B :: Γ) t T →
      LevelStagedCastGuard definitions stage false (proofErase Γ A) (proofErase Γ C) →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.bvar i))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions (stage+1))
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro stage mode Γ u A B C E i t T left right heq hΓ hA hC HL hf ht HA RL RR
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact Strengthening.staged_converted_lookup_eta_consumer_core heq sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_level_core_confluence (fun H => H))
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq) hΓ hA hC HL hf ht HA RL RR

omit [Params] in
/-- Concrete converted-domain coverage: reflexively casting the declared input
type changes the written eta annotation. Its finite domain certificate and
converted function typing are both constructed here. The caller supplies no
native recovery or domain-comparison oracle. -/
theorem EnvironmentCore.cast_domain_lookup_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ u C E i q}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ C (.sort u) → Lookup Γ i (.forallE C E) →
      env.HasType U Γ q (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let A := typeCast (.succ u) (.sort u) (.sort u) q C
      ∀ {t T left right}, env.HasType U (.forallE A E :: Γ) t T →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.bvar i))) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 2)
          (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro mode Γ u C E i q heq hΓ hC HL hq A t T left right ht RL RR
  have hu := hC.sort_r henv hΓ
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have HAC := IsDefEq.typeCast_refl henv heq (by exact hu) hΓ hS hq hC
  have hfC : env.HasType U Γ (.bvar i) (.forallE C E) := .bvar HL
  obtain ⟨_, hPi⟩ := hfC.isType henv hΓ
  obtain ⟨_, _, hE⟩ := hPi.forallE_inv henv
  have hf : env.HasType U Γ (.bvar i) (.forallE A E) :=
    (IsDefEq.forallEDF HAC.symm hE).defeq hfC
  have HS : LevelStagedCastGuard definitions 0 true (proofErase Γ (.sort u)) (proofErase Γ (.sort u)) :=
    .core (.join hΓ hS hS ⟨_, .refl, .refl⟩)
  have HA : LevelStagedCastGuard definitions 1 false (proofErase Γ A) (proofErase Γ C) :=
    .cast (by exact hu) hΓ hS hS hq hC HS
  exact staged_converted_lookup_eta_consumer_core henv U heq hΓ HAC.hasType.1 hC HL hf ht HA RL RR

end Lean4Lean.VEnv.Strengthening
