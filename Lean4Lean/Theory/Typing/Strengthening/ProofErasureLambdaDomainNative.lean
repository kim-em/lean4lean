import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery

/-! # Native type readout of historical lambda-domain observations

The application case transports the observed dependent result type by ordinary
substitution. It never substitutes the function's native recovery derivation,
and hence does not need recovery of the argument at the written cut domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
variable [Params]

/-- A retained value cannot have an assigned type in a universe equivalent
to Prop. This uses ordinary typing, not a recovery or joining premise. -/
theorem retained_type_level_ne_zero
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hA : env.HasType univs Γ A (.sort u)) (hn : ¬ IsProof Γ x) : ¬ u ≈ .zero := by
  intro hu
  exact hn ⟨A, hx, (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA⟩

namespace LambdaDomainObservation
variable {D : PureObservation.Definitions} {Γ : List VExpr} {anchor : ProofShape}

/-- Every native output of an observed term satisfies its recursive type
demand. Control annotations provide historical input demands, while arbitrary
typed argument substitution transports dependent result observations. This is
independent of exact native-cut stability and of all type-fork joining claims. -/
theorem Obs.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : Obs D Γ anchor n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ anchor n Δ S)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    LowerDomainDemand D Γ anchor o n Δ out := by
  induction H generalizing Γ' e T out with
  | var hi =>
    cases EΓ
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨C, hl⟩ := ht.bvar_inv henv.orderedStrong hΓ'
    have hvar : env.HasType univs Γ' (.bvar _) C := .bvar hl
    obtain ⟨u, hC⟩ := hvar.isType henv hΓ'
    have EC := erasedTypeOracle_valid hΓ' hl
    rw [← proofEraseCtx_oracle] at EC
    have HD := HS _ _ hi
    have RC := RN.bvar_compute
    rw [EC] at HD RC
    exact HD.compute_type heq hs hΓ hΓ' W hC RC
  | @payload n Δ rawA rawb S HP =>
    cases EΓ
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ'
    have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
    obtain ⟨C, RC, RP⟩ := RN.lam_compute
    obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb
      (by simpa only [proofEraseCtx, EA, Eb] using RC)
    obtain ⟨v, hC⟩ := hbC.isType henv hΓA
    have hPi := HasType.forallE hA hC
    have hn : ¬ IsProof Γ' (.lam A b) := fun hp => RN.ne_proof (Ee ▸ proofErase_eq_proof.2 hp)
    have hu := retained_type_level_ne_zero hΓ' (HasType.lam hA hbC) hPi hn
    have EP : proofErase Γ' (.forallE A C') =
        .forallE (proofErase Γ' A) (proofErase (A :: Γ') C') := if_neg (not_isProof_of_sort hΓ' hPi)
    have HI : LowerDomainDemand D Γ anchor .pi n (proofEraseCtx Γ')
        (proofErase Γ' (.forallE A C')) := by
      rw [EP]
      simp only [LowerDomainDemand, NativeTypeDemand]
      refine ⟨_, hu, ProofShape.IndexedControlObservation.Obs.payload
        ⟨Γ', .forallE A C', hΓ', rfl, hPi, EP⟩ ?_⟩
      simpa only [LowerDomainHistory, EA] using HP
    apply HI.compute_type heq hs hΓ hΓ' W hPi
    simpa only [EP, EA, EC] using RP
  | @lam Δ A u keys n S b o SD HD HB ih =>
    cases EΓ
    obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨v, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ'
    have hΓA : OnCtx (A₀ :: Γ') (env.IsType univs) := ⟨hΓ', v, hA⟩
    have W' : Ctx.LiftN (n+1) 0 Γ (A₀ :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
    have EΓA : proofEraseCtx (A₀ :: Γ') = A :: proofEraseCtx Γ' := by simp only [proofEraseCtx, EA]
    obtain ⟨C, RC, RP⟩ := RN.lam_compute
    have HC := ih hΓA W' hb EΓA Eb (HS.cons SD HD) RC
    obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb
      (by simpa only [proofEraseCtx, EA, Eb] using RC)
    obtain ⟨w, hC⟩ := hbC.isType henv hΓA
    have hPi := HasType.forallE hA hC
    have hn : ¬ IsProof Γ' (.lam A₀ b₀) := fun hp => RN.ne_proof (Ee ▸ proofErase_eq_proof.2 hp)
    have hu := retained_type_level_ne_zero hΓ' (HasType.lam hA hbC) hPi hn
    have EP : proofErase Γ' (.forallE A₀ C') =
        .forallE (proofErase Γ' A₀) (proofErase (A₀ :: Γ') C') := if_neg (not_isProof_of_sort hΓ' hPi)
    have HI : LowerDomainDemand D Γ anchor (.app keys o) n (proofEraseCtx Γ')
        (proofErase Γ' (.forallE A₀ C')) := by
      rw [EP]
      simp only [LowerDomainDemand, NativeTypeDemand]
      refine ⟨_, hu, ProofShape.IndexedControlObservation.Obs.payload
        ⟨Γ', .forallE A₀ C', hΓ', rfl, hPi, EP⟩ ?_⟩
      exact ⟨fun key hk => EA ▸ HD key hk, by simpa only [EA, EC] using HC⟩
    apply HI.compute_type heq hs hΓ hΓ' W hPi
    simpa only [EP, EA, EC] using RP
  | @app n Δ S f keys o a HF HX ihf _ =>
    cases EΓ
    obtain ⟨f₀, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨A, B, hf, hx⟩ := ht.app_inv henv hΓ'
    obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
    have HN := ihf hΓ' W hf rfl Ef HS RF
    have HY := HN.function_parts.2
    obtain ⟨A', B', hfPi, EA, EB⟩ := proofErase_scoped_recovered_pi_descend
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' hΓ'
      (Ctx.LiftN.zero []) hf (by simpa only [List.length_nil, ProofShape.liftN_zero, Ef] using RF)
    simp only [List.length_nil, ProofShape.liftN_zero] at EA EB
    have hxA := argument_at_displayed_domain hΓ' hf hfPi hx
    obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ'
    obtain ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv henv
    have hΓA : OnCtx (A' :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
    have WI : ContextSubstitution (X :: proofEraseCtx Γ') (proofEraseCtx Γ')
        (ProofShape.Subst.one a) := by
      intro Γ₀ hΓ₀ EΓ₀
      have Wraw : ContextSubstitution (proofEraseCtx (A' :: Γ')) (proofEraseCtx Γ')
          (ProofShape.Subst.one (proofErase Γ' x)) :=
        ContextSubstitution.of_typed hΓ'
          (Ctx.InstN.zero.substEq hΓA hxA) (erasedSubstAgreement_one hΓA hxA)
      simpa only [proofEraseCtx, EA, Ex] using Wraw hΓ₀ (by simpa only [proofEraseCtx, EA] using EΓ₀)
    have HF : FixedTail n n ProofShape.Subst.id := by intro i; rfl
    have HY' := HY.subst lower_domain_history_substitution WI HF.cons
    have hBI := hB.instN henv.ordered Ctx.InstN.zero hxA
    have EI : proofErase Γ' (B'.inst x) = Y.inst a := by
      rw [proofErase_instN hΓA hxA Ctx.InstN.zero hB, EB, Ex]
    have HI : LowerDomainDemand D Γ anchor o n (proofEraseCtx Γ') (proofErase Γ' (B'.inst x)) := by
      simpa only [EI, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HY'
    apply HI.compute_type heq hs hΓ hΓ' W hBI
    simpa only [EI] using RC

end LambdaDomainObservation
end Lean4Lean.VEnv.Strengthening
