import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaComputed
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedSpecialization

/-! # Read an inner singleton through both Eq argument histories

Reify the outer five arguments below the unused binders before opening the eta
domain. The computed fresh-body singleton then descends in the extended lower
context and specializes at the actual next argument. Only semantic equality
is substituted; both guarded computation histories remain in their scopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem typed_const_levels_wf
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args)) :
    ∀ l ∈ ls, l.WF univs := by
  obtain ⟨Γ, e, T, hΓ, _, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, _⟩ := proofErase_const_spine_inv Ee
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩
  exact (HasType.const_inv henv hΓ hc).choose_spec.2.1

/-- Either singleton form inside the first eta body reads the original lower
Eq equation, even when both the outer arguments and the fresh body components
have computed. Its guard is lowered before the fresh binder is specialized. -/
theorem pi_inert_eq_eta_inner_singleton_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (HL : List.Forall₂ (· ≈ ·) [v,w] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      ((([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof]) (pre ++ pending))
    (hshort : pre.length ≤ 4)
    (HT : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Γ') rawA u)
    (HLbody : List.Forall₂ (· ≈ ·) ls bodyLs)
    (HAbody : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: proofEraseCtx Γ'))
      (pre.map (·.liftN 1) ++ [etaArgument u]) (bodyPre ++ bodyPending))
    (HTinner : TypedSource (rawA :: proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre))
    (HG : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D singletonStage)
        (rawA :: proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target ∨
      ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D singletonStage)
        (rawA :: proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target) :
    env.IsDefEq univs Γ a b α := by
  obtain ⟨v₁, w₁, rfl⟩ : ∃ v₁ w₁, ls = [v₁,w₁] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  obtain ⟨v₂, w₂, rfl⟩ : ∃ v₂ w₂, bodyLs = [v₂,w₂] := by
    cases HLbody with | cons _ HLbody => cases HLbody with | cons _ HLbody => cases HLbody; exact ⟨_, _, rfl⟩
  obtain ⟨hv, hw, _, ha, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v,w]) (.const ``Eq.rec [v₁,w₁]) :=
    ⟨_, .constDF heq.2.2.1 (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact hv
      · exact hw) (typed_const_levels_wf HT) (by rfl) HL⟩
  have HA5 := Lean4Lean.List.forall₂_take HA 5
  have HA5 : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ((pre ++ pending).take 5) := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero] using HA5
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  obtain ⟨full, HP, EP, HE⟩ := proofErase_scoped_spine_arguments_descend hd hΓ hΓ' W HC ht HA5
  cases HP with | cons Hα HP =>
  cases HP with | cons Ha HP =>
  cases HP with | cons HM HP =>
  cases HP with | cons Hminor HP =>
  cases HP with | cons Hb HP =>
  cases HP
  rename_i α₁ a₁ M₁ minor₁ b₁
  let full := [α₁,a₁,M₁,minor₁,b₁]
  let lowerPre := full.take pre.length
  have EPpre : ((lowerPre.map (proofErase Γ)).map (·.liftN count offset)) = pre := by
    dsimp only [lowerPre]
    rw [List.map_take, List.map_take, EP, List.take_take, Nat.min_eq_left (by omega), List.take_left]
  have hfull : env.HasType univs Γ (eqRecBeforeMajor v₁ w₁ α₁ a₁ M₁ minor₁ b₁) T := HE.hasType.2
  have hnfull : ¬ IsProof Γ (eqRecBeforeMajor v₁ w₁ α₁ a₁ M₁ minor₁ b₁) :=
    fun hp => hn ((isProof_congr hΓ HE).2 hp)
  cases ED : full.drop pre.length with
  | nil =>
    have Hlen := congrArg List.length ED
    simp only [List.length_drop, full, List.length_cons, List.length_nil] at Hlen
    omega
  | cons x rest =>
    have Efull : lowerPre ++ x :: rest = full := by
      rw [← ED]; exact List.take_append_drop _ _
    have hsplit : env.HasType univs Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v₁,w₁]) lowerPre) (x :: rest)) T := by
      rw [← VExpr.mkApps_append, Efull]; exact hfull
    obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
    have hnp := nonproof_spine_head hΓ hsplit (by
      simpa only [← VExpr.mkApps_append, Efull, full, eqRecBeforeMajor] using hnfull)
    have Eprefix : (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v₁,w₁]) lowerPre)).liftN count offset =
        ProofShape.mkApps (.const ``Eq.rec [v₁,w₁]) pre := by
      rw [proofErase_const_spine hΓ hp hnp, ProofShape.liftN_mkApps, EPpre]; rfl
    obtain ⟨A, B, hf, EA, _⟩ := proofErase_scoped_recovered_pi_descend
      (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) hΓ hΓ' W hp
      (by simpa only [Eprefix] using RN)
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ SD).descend hΓ hΓ' W hA
    obtain ⟨Tx, hfx⟩ := VExpr.WF.of_mkApps henv hΓ (f := .app _ x) ⟨_, hsplit⟩
    have hfx : env.HasType univs Γ (.app (VExpr.mkApps (.const ``Eq.rec [v₁,w₁]) lowerPre) x) Tx := hfx
    obtain ⟨_, _, hf', hx⟩ := hfx.app_inv henv hΓ
    have hxA := argument_at_displayed_domain hΓ hf' hf hx
    have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
      rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA]
    have HR : env.IsDefEq univs Γ a₁ b₁ α₁ := by
      rcases HG with HG | HQ
      · have RL : ScopedCompute (ErasedStaticStructureEtaExpansionStage D bodyStage)
            (rawA :: proofEraseCtx Γ') (.const ``Eq.rec [v₁,w₁]) (.const ``Eq.rec [v₂,w₂]) :=
          .base (erased_static_structure_eta_expansion_stage_mono (Nat.zero_le bodyStage)
            (show ErasedStaticStructureEtaExpansionStage D 0 _ _ _ from
              .inl (.inr (.const HLbody (typed_const_levels_wf HTinner)))))
        have Hbody : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D singletonStage)
            (proofEraseCtx (A.liftN count offset :: Γ'))
            (ProofShape.mkApps (.const ``Eq.rec [v₂,w₂]) ((bodyPre ++ bodyPending).take bodyPre.length)) target := by
          simpa only [Ectx, List.take_left] using HG
        exact proofErase_recovered_singleton_eq_computed_fresh_eta_descend heq
          (erased_static_structure_eta_expansion_stage_descent heq hs bodyStage)
          (erased_static_structure_eta_expansion_stage_certificate_descent heq hs singletonStage)
          hΓ hΓ' W hA hf hnp hxA hfull Efull
          (by simpa only [Ectx, EPpre] using HAbody.imp (fun _ _ R => R.mono pi_inert_stage_embed))
          (by simpa only [Ectx] using RL) Hbody
      · exact pi_inert_eq_computed_fresh_eta_readout heq hs hΓ hΓ' W hA hf hxA hfull Efull
          (by simpa only [Ectx, EPpre] using HAbody) (by simpa only [Ectx] using HQ)
    exact ((Ha.trans henv hΓ HR.toU).trans henv hΓ Hb.symm).of_l henv hΓ ha

/-- The inner root left after both singleton readouts: an earlier native
function eta expansion. Eliminating this nested eta is still open. -/
def EqEtaRemainingRoot (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (source target : ProofShape) : Prop :=
  ∃ k, k < n ∧ NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target

/-- Read either selected inner singleton back to the original equation,
or retain the same cut with native function eta as its only root form.
The outer and inner component histories are both used; no cut is reselected. -/
theorem CountedEtaBodySpineCut.read_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (HL : List.Forall₂ (· ≈ ·) [v,w] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      ((([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof]) (pre ++ pending))
    (hshort : pre.length ≤ 4)
    (HT : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort (proofEraseCtx Γ') A u)
    (H : CountedEtaBodySpineCut D n (proofEraseCtx Γ') ``Eq.rec ls pre A u pending out ct
      (EqEtaGuardedRoot D)) :
    env.IsDefEq univs Γ a b α ∨
      CountedEtaBodySpineCut D n (proofEraseCtx Γ') ``Eq.rec ls pre A u pending out ct
        (EqEtaRemainingRoot D) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩ := H
  have finish (HG' : EqEtaRemainingRoot D m (A :: proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec ls') bodyPre) target) :
      CountedEtaBodySpineCut D n (proofEraseCtx Γ') ``Eq.rec ls pre A u pending out ct
        (EqEtaRemainingRoot D) :=
    ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
      hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG'⟩
  rcases HG with HQ | ⟨k, hk, HG | HE⟩
  · exact .inl (pi_inert_eq_eta_inner_singleton_readout heq hs hΓ hΓ' W ht hn HL HA
      hshort HT RN SD HLbody HAbody HTR (.inr HQ))
  · exact .inl (pi_inert_eq_eta_inner_singleton_readout heq hs hΓ hΓ' W ht hn HL HA
      hshort HT RN SD HLbody HAbody HTR (.inl HG))
  · exact .inr (finish ⟨k, hk, HE⟩)

end Lean4Lean.VEnv.Strengthening
