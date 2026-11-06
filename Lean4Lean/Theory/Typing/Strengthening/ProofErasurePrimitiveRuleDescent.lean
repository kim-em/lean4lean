import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCertificateDescent

/-! # Descent of one primitive to one primitive

The certificate interface retains a lower computation, but does not bound its
primitive count. Here every primitive in the full structure/function-eta union
is reconstructed as one lower primitive at the same stage. Guard computations
are retained separately; this result does not bound their internal proof size.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private GuardedSingleton.family_guard_certificate_below
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredStageCertificateDescent
variable [Params]

/-- One primitive above an inserted binder block gives one primitive below,
with an actual typed representative and exactly the original lifted output.
Only outer computational primitives are counted; guard derivations may contain
arbitrary finite computations. This is stronger than certificate descent. -/
def ErasedScopedPrimitiveRuleDescent
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' n k e T out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → env.HasType univs Γ e T →
    Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k) out →
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      Target (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      (proofErase Γ e').liftN n k = out

/-- A single lower primitive also supplies the ordinary descent certificate. -/
theorem ErasedScopedPrimitiveRuleDescent.certificate
    (H : ErasedScopedPrimitiveRuleDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent Step Target := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  obtain ⟨e', HE, HR, Ee⟩ := H hΓ hΓ' W ht R
  exact ⟨e', HE, .base HR, Ee⟩

private theorem erased_joint_zero_rule_descent (hs : D.Sound env univs) :
    ErasedScopedPrimitiveRuleDescent (ErasedJointStage D 0) (ErasedJointStage D 0) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨e', HE, Ee⟩ := ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
    hΓ hΓ' W ht H
  refine ⟨e', HE, ?_, Ee⟩
  have HR := erased_iota_primitive_subst
    (σ := ProofShape.Subst.retract (.consN (.skipN .refl n) k)) H
  rw [← Ee, ← ProofShape.lift'_consN_skipN, ← ProofShape.lift'_consN_skipN,
    ProofShape.subst_retract_lift', ProofShape.subst_retract_lift'] at HR
  exact HR

private theorem erased_level_primitive_rule_descent :
    ErasedScopedPrimitiveRuleDescent (fun _ => LevelPrimitive univs)
      (fun _ => LevelPrimitive univs) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨e', HE, Ee⟩ := erased_level_primitive_descent hΓ hΓ' W ht H
  refine ⟨e', HE, ?_, Ee⟩
  have HR := H.subst (τ := ProofShape.Subst.retract (.consN (.skipN .refl n) k))
  rw [← Ee, ← ProofShape.lift'_consN_skipN, ← ProofShape.lift'_consN_skipN,
    ProofShape.subst_retract_lift', ProofShape.subst_retract_lift'] at HR
  exact HR

private theorem erased_constantExpansion_rule_descent :
    ErasedScopedPrimitiveRuleDescent (fun _ => ConstantExpansion)
      (fun _ => ConstantExpansion) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hn =>
    have hne : ¬ IsProof Γ e := by
      intro hp
      exact hn (by rw [proofErase_eq_proof.2 hp]; rfl)
    refine ⟨_, (constantExpansion_equal ht).symm, ?_, ?_⟩
    · rw [proofErase_constantExpansion hΓ ht hne]
      exact (.intro (fun H => hne (proofErase_eq_proof.1 H)))
    · rw [proofErase_constantExpansion hΓ ht hne, constantExpansion_liftN]

private theorem erased_nativeIdentityExpansion_rule_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveRuleDescent (NativeIdentityExpansion Step)
      (NativeIdentityExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R =>
    obtain ⟨A, he, RA, EA⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W ht rfl R
    have hn : ¬ IsProof Γ e := fun hp => RA.ne_proof (proofErase_eq_proof.2 hp)
    refine ⟨_, (nativeIdentityExpansion_equal he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
    · rw [proofErase_nativeIdentityExpansion hΓ he hn]
      exact (.intro RA)
    · rw [proofErase_nativeIdentityExpansion hΓ he hn]
      simp only [ProofShape.liftN, EA, liftVar, Nat.zero_lt_succ, ↓reduceIte]

private theorem erased_nativeEtaExpansion_rule_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveRuleDescent (NativeEtaExpansion Step)
      (NativeEtaExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R S =>
    obtain ⟨A, B, he, RN, EA, _⟩ := proofErase_recovered_pi_certificate_descend hstep hΓ hΓ' W ht R
    obtain ⟨_, hPi⟩ := he.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ S).descend hΓ hΓ' W hA
    have hn : ¬ IsProof Γ e := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
    refine ⟨_, (IsDefEq.eta he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
    · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
      exact (.intro RN (DomainSort.of_typed hΓ hA))
    · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
      simp only [ProofShape.liftN, etaArgument_liftN, EA]
      rw [ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)]

private theorem erased_nativeMaskedStructureExpansion_rule_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveRuleDescent (NativeMaskedStructureExpansion Step)
      (NativeMaskedStructureExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hi hx ha hp RN =>
    rename_i family info ls rawPs
    obtain ⟨A, heA, RL, EA⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W ht rfl RN
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
      exact (.intro hi hx ha (by simpa only [List.length_map] using hps) (by simpa only [Es] using RL))
    · rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc, nativeStructureOutput_liftN, ← Eps]

private theorem erased_carrier_recovered_singleton_rule_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveRuleDescent (ProofShape.CarrierRecoveredSingletonPrimitive Step)
      (ProofShape.CarrierRecoveredSingletonPrimitive Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨_, R⟩ := H
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv hsrc
    obtain ⟨original, rfl, Hargs⟩ := proofErase_const_spine_inv Es
    rw [Hargs] at Eargs
    have hargs := (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2
    have hmap : (original.map (·.liftN n k)).map (proofErase Γ') = args := by
      rw [Eargs]
      simp only [List.map_map]
      apply List.map_congr_left
      intro a ha
      obtain ⟨_, hat⟩ := hargs a ha
      exact proofErase_liftN hΓ hΓ' W hat
    have hup : env.HasType univs Γ'
        (VExpr.mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) (T.liftN n k) := by
      simpa only [VExpr.liftN_mkApps, VExpr.liftN] using ht.weakN henv W
    have hlenargs : (original.map (·.liftN n k)).length = C.arity := by
      simpa only [List.length_map] using (congrArg List.length hmap).trans ha
    obtain ⟨program, hg, hd, HG'⟩ := V.realizeWith heq hΓ' hlenargs ⟨_, hup⟩
      (by rwa [hmap]) (by rwa [hmap])
    have HC := V.checkWith heq (erased_carrier_recovered_family_descent hstep.descent) hΓ' hg ⟨_, hup⟩ HG'
    obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
    have hlen : C.levels.length = C.data.uvars := by
      rw [hl] at hll
      exact hll.trans (RecursorData.singletonEquation_uvars he)
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
    obtain ⟨lower, hgl⟩ := V.generate (args := original) (by simpa only [List.length_map] using hlenargs)
    let ρ := (Lift.refl.skipN n).consN k
    have hback := RecursorData.singletonUnfolding_lift' henv V.registered V.large V.zero V.recType_eq
      (V.registered.recursorType_closed henv V.recType_eq) hgl (ρ := ρ)
    have hgρ : C.data.singletonUnfolding env univs C.levels (original.map (·.lift' ρ)) = some program := by
      simpa only [ρ, VExpr.lift'_consN_skipN] using hg
    have hprogram := RecursorData.singletonUnfolding_unique hgρ hback
    have HGren := hprogram ▸ HG'
    have HGlo := GuardedSingleton.family_guard_certificate_below heq hstep W hΓ hΓ'
      V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGren
    have HGsem := GuardedSingleton.family_guard_with_below heq (erased_carrier_recovered_family_descent hstep.descent)
      W hΓ hΓ' V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGren
    have HClo := GuardedSingleton.check_of_family_conversion henv heq hΓ V.registered V.large V.zero
      V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGsem
    have HH := (show env.IsDefEqU univs Γ _ _ from ⟨_, HClo.defeq henv hΓ⟩).of_l henv hΓ ht
    have hn : ¬ IsProof Γ (VExpr.mkApps (.const C.data.name C.levels) original) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (Es.symm.trans (proofErase_eq_proof.2 hp))
    have hnup := mt (isProof_liftN hΓ hΓ' W ht).1 hn
    have hnup' : ¬ IsProof Γ' (VExpr.mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) := by
      simpa only [VExpr.liftN_mkApps, VExpr.liftN] using hnup
    refine ⟨lower.rhs, HH, ?_, ?_⟩
    · rw [proofErase_const_spine hΓ ht hn, V.output_eq heq hΓ hgl HClo hn]
      exact ⟨⟨Γ, _, _, hΓ, rfl, ht, proofErase_const_spine hΓ ht hn⟩,
        .intro V (by simpa only [List.length_map] using hlenargs)
          (V.telescope_eq hΓ hgl ⟨_, ht⟩) ((V.guardWith_iff heq hΓ hgl ⟨_, ht⟩).2 HGlo)⟩
    have Erhs : program.rhs = lower.rhs.liftN n k := by
      rw [hprogram]
      simpa only [ρ, VExpr.lift'_consN_skipN] using
        (RecursorData.PrefixUnfolding.rename_rhs (ρ := ρ)
          (ClosedSingleton.generated_template_closed henv V.registered V.large V.zero hgl))
    rw [← proofErase_liftN hΓ hΓ' W HH.hasType.2, ← Erhs,
      V.output_eq heq hΓ' hg HC hnup', hd, hmap]

private theorem erased_computed_joint_prefix_rule_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveRuleDescent (ProofShape.ComputedJointPrefixPrimitive Step) (ProofShape.ComputedJointPrefixPrimitive Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨αs, as, Ms, ms, bs, E, Eα, Ea, EM, Em, Eb⟩ :=
      ProofShape.liftN_eqRecBeforeMajor_inv hsrc
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv E
    rw [← Hα] at Eα
    rw [← Ha] at Ea
    rw [← HM] at EM
    rw [← Hm] at Em
    rw [← Hb] at Eb
    rw [← Eα, ← Ea, ← Eb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := proofErase_computed_joint_carrier_descend hstep.descent hΓ hΓ' W ha hb HC
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at E
      cases E
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    have CC := proofErase_computed_joint_carrier_certificate_descend hstep hΓ hΓ' W ha hb HC
    refine ⟨_, HH, ?_, ?_⟩
    · rw [E, show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
        .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
        proofErase_eqProofType heq hw hΓ hα ha hb,
        proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, ← Hα, ← Ha, ← HM, ← Hm, ← Hb]
      exact (.intro CC)
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    simp only [ProofShape.liftN, ProofShape.eqProofType,
      ← ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _), Eα, Ea, Eb, Em]

/-- Every finite structure/function-eta stage descends one outer primitive
without increasing its stage or replacing it by several computational steps.
The guard descent uses the existing same-stage certificate theorem. -/
theorem erased_static_structure_eta_expansion_stage_rule_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveRuleDescent (ErasedStaticStructureEtaExpansionStage D stage)
      (ErasedStaticStructureEtaExpansionStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with (H | H) | H
    · obtain ⟨e', HE, R, E⟩ := erased_joint_zero_rule_descent hs hΓ hΓ' W ht H
      exact ⟨e', HE, .inl (.inl R), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_level_primitive_rule_descent hΓ hΓ' W ht H
      exact ⟨e', HE, .inl (.inr R), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_constantExpansion_rule_descent hΓ hΓ' W ht H
      exact ⟨e', HE, .inr R, E⟩
  | succ stage ih =>
    have HC : ErasedScopedPrimitiveCertificateDescent (ErasedStaticStructureEtaExpansionStage D stage)
        (ErasedStaticStructureEtaExpansionStage D stage) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, .inl R, E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_carrier_recovered_singleton_rule_descent heq HC hΓ hΓ' W ht H
      exact ⟨e', HE, .inr (.inl R), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_computed_joint_prefix_rule_descent heq HC hΓ hΓ' W ht H
      exact ⟨e', HE, .inr (.inr (.inl R)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeIdentityExpansion_rule_descent HC hΓ hΓ' W ht H
      exact ⟨e', HE, .inr (.inr (.inr (.inl R))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeEtaExpansion_rule_descent HC hΓ hΓ' W ht H
      exact ⟨e', HE, .inr (.inr (.inr (.inr (.inl R)))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeMaskedStructureExpansion_rule_descent HC hΓ hΓ' W ht H
      exact ⟨e', HE, .inr (.inr (.inr (.inr (.inr R)))), E⟩

/-- The full union likewise descends each primitive as a single primitive.
This supplies a quantitative interface, not a confluence or normalization claim. -/
theorem erased_static_structure_eta_expansion_union_rule_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveRuleDescent (ErasedStaticStructureEtaExpansionUnion D)
      (ErasedStaticStructureEtaExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  obtain ⟨e', HE, R, E⟩ := erased_static_structure_eta_expansion_stage_rule_descent heq hs stage hΓ hΓ' W ht H
  exact ⟨e', HE, ⟨stage, R⟩, E⟩

end Lean4Lean.VEnv.Strengthening
