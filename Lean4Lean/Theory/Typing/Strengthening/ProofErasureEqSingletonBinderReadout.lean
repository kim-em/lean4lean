import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializedReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixArity

/-! # General-singleton readout through two binder insertions

Remove the later binder block while retaining component computation
certificates. These paths permit a second descent through the original block,
after which the target completion reads the semantic Eq equation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Reify a component history while retaining its lower computation
certificates, not just semantic equalities. This permits another ambient
descent after the current binder block has been removed. -/
theorem proofErase_scoped_spine_arguments_certificate_descend
    (hsource : ErasedScopedPrimitiveCertificateDescent Source Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hf : env.IsDefEqU univs Γ f g)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T)
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((args.map (proofErase Γ)).map (·.liftN count offset)) raw) :
    ∃ args', List.Forall₂ (env.IsDefEqU univs Γ) args args' ∧
      List.Forall₂ (ScopedCompute Target (proofEraseCtx Γ))
        (args.map (proofErase Γ)) (args'.map (proofErase Γ)) ∧
      ((args'.map (proofErase Γ)).map (·.liftN count offset)) = raw ∧
      env.IsDefEq univs Γ (VExpr.mkApps f args) (VExpr.mkApps g args') T := by
  induction args generalizing f g raw with
  | nil => cases HA; exact ⟨[], .nil, .nil, rfl, hf.of_l henv hΓ ht⟩
  | cons x xs ih =>
    cases HA with
    | cons RX RXS =>
      obtain ⟨Tapp, happ⟩ := VExpr.WF.of_mkApps henv hΓ
        (show VExpr.WF env univs Γ (VExpr.mkApps (.app f x) xs) from ⟨_, ht⟩)
      have happ : env.HasType univs Γ (.app f x) Tapp := happ
      obtain ⟨A, B, hft, hx⟩ := happ.app_inv henv hΓ
      obtain ⟨x', HX, RX', EX⟩ := proofErase_scoped_compute_certificate_descend
        hsource hΓ hΓ' W hx rfl RX
      have HF := IsDefEq.appDF (hf.of_l henv hΓ hft) HX
      obtain ⟨xs', HS, RS, ES, HE⟩ := ih HF.toU ht RXS
      exact ⟨x' :: xs', .cons HX.toU HS, .cons RX' RS,
        by simp only [List.map_cons, EX, ES], HE⟩

/-- Read a general singleton after component computation across two binder
blocks, at arbitrary insertion depths. The first descent retains lower paths
for the second; neither block requires a target substitution or inhabitants. -/
theorem EqPrefixSpecialization.read_computed_singleton_two_blocks
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveCertificateDescent Source Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hΓ'' : OnCtx Γ'' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (W' : Ctx.LiftN count' offset' Γ' Γ'')
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ''))
      (((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN count' offset')) raw)
    (HG : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ'')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.take arity)) target) :
    env.IsDefEq univs Δ a b α := by
  let lifted := pre.map (·.liftN count offset)
  have hf' : env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) lifted)
      (F.liftN count offset) := by
    simpa only [lifted, VExpr.liftN_mkApps, VExpr.liftN] using hf.weakN henv W
  have HC' : env.IsDefEqU univs Γ' (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) := by
    simpa only [VExpr.liftN] using HC.weakN henv.ordered W
  have EL : lifted.map (proofErase Γ') = (pre.map (proofErase Γ)).map (·.liftN count offset) := by
    simp only [lifted, List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, hte⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 e he
    exact proofErase_liftN hΓ hΓ' W hte
  obtain ⟨pre', _, RC, EP, HE⟩ := proofErase_scoped_spine_arguments_certificate_descend
    hsource hΓ' hΓ'' W' HC' hf' (by simpa only [EL] using HA)
  have hn' : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) lifted) := by
    simpa only [lifted, VExpr.liftN_mkApps, VExpr.liftN] using
      mt (isProof_liftN hΓ hΓ' W hf).1 hn
  have hnnew : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') :=
    fun hp => hn' ((isProof_congr hΓ' HE).2 hp)
  have hsplit : env.HasType univs Γ'
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.take arity)) (pre'.drop arity))
      (F.liftN count offset) := by
    rw [← VExpr.mkApps_append, List.take_append_drop]; exact HE.hasType.2
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ' ⟨_, hsplit⟩
  have hnp := nonproof_spine_head hΓ' hsplit (by
    simpa only [← VExpr.mkApps_append, List.take_append_drop] using hnnew)
  have HG' : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ'')
      ((proofErase Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.take arity))).liftN count' offset')
      target := by
    rw [proofErase_const_spine hΓ' hp hnp, ProofShape.liftN_mkApps]
    simpa only [← EP, List.map_take, ProofShape.liftN] using HG
  obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep hΓ' hΓ'' W' hp HG'
  rw [proofErase_const_spine hΓ' hp hnp] at HL
  apply H.read_computed_singleton heq hsource.descent hstep hΓ hΓ' W hΔ ht hf hn HC
    (by simpa only [EL] using RC)
  simpa only [List.map_take] using HL

/-- Every general singleton on the fresh eta-body spine reads the original
target equation without filling the new binder. Valid canonical Eq singleton
code bounds its arity by five, so the proof-major slot can be discarded before
the two binder descents. No target proof or extra prefix bound is assumed. -/
theorem EqPrefixSpecialization.read_singleton_after_eta
    (heq : env.HasCanonicalEq) (hguard : ErasedScopedPrimitiveDescent Guard)
    (hsource : ErasedScopedPrimitiveCertificateDescent Source Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v' w' α' a' M' minor' b'))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Γ')
      ((proofErase Γ (eqRecBeforeMajor v' w' α' a' M' minor' b')).liftN count offset)
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Γ') rawA u)
    (HA : List.Forall₂ (ScopedCompute Source (rawA :: proofEraseCtx Γ'))
      (((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++
        [etaArgument u]) (rawPre ++ pending))
    (HG : CarrierRecoveredSingletonPrimitive Step (rawA :: proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawPre) target) :
    env.IsDefEq univs Δ a b α := by
  have hshort := HG.2.eq_rec_arity_le heq
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ' W hf RN
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hA := (EA ▸ SD).descend hΓ hΓ' W hA
  have hΓA : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
  have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA]
  have HA5 := Lean4Lean.List.forall₂_take HA 5
  have HA5 : List.Forall₂ (ScopedCompute Source (proofEraseCtx (A.liftN count offset :: Γ')))
      ((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1))
      ((rawPre ++ pending).take 5) := by
    simpa only [Ectx, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero] using HA5
  apply H.read_computed_singleton_two_blocks heq hsource hstep hΓ hΓ' hΓA W Ctx.LiftN.one hΔ
    ht hf hn HC HA5 (arity := rawPre.length)
  simpa only [Ectx, List.take_take, Nat.min_eq_left hshort, List.take_left] using HG

/-- Both singleton forms reached after eta on a full five-argument prefix
read the same original target equation. Body computation and root guards may
use different finite stages; neither branch specializes the proof-major binder. -/
theorem EqPrefixSpecialization.read_singletons_after_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v' w' α' a' M' minor' b'))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) (proofEraseCtx Γ')
      ((proofErase Γ (eqRecBeforeMajor v' w' α' a' M' minor' b')).liftN count offset)
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Γ') rawA u)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: proofEraseCtx Γ'))
      (((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++
        [etaArgument u]) (rawPre ++ pending))
    (HG : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (rawA :: proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawPre) target ∨
      ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (rawA :: proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawPre) target) :
    env.IsDefEq univs Δ a b α := by
  rcases HG with HG | HQ
  · exact H.read_singleton_after_eta heq
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs bodyStage)
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs rootStage)
      hΓ hΓ' W hΔ ht hf hn HC RN SD (HA.imp (fun _ _ R => R.mono pi_inert_stage_embed)) HG
  · exact H.read_computed_guard_after_eta heq
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs (max bodyStage rootStage))
      hΓ hΓ' W hΔ ht hf RN SD
      (HA.imp (fun _ _ R => R.mono (fun H =>
        erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left bodyStage rootStage) H.1)))
      (HQ.mono (erased_static_structure_eta_expansion_stage_mono (Nat.le_max_right bodyStage rootStage)))

end Lean4Lean.VEnv.Strengthening
