import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery

/-! # Native type histories of higher-order constructor control programs

The observer interprets arbitrary applications and lambdas through recursive
data-type demands. Its native application case uses ordinary substitution of
an actual argument into the function's type observation, never substitution
of the function's native derivation through a newly assumed native image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
variable [Params]

namespace ConstructorControlObservation
variable {D : PureObservation.Definitions} {Γ : List VExpr} {origin : ProofShape}
variable {r : Name} {info : VProjectionInfo}

/-- Every native output of an observed term satisfies its recursive type
demand. Control annotations provide historical input demands, while arbitrary
typed argument substitution transports dependent result observations. This is
independent of exact native-cut stability and of all type-fork joining claims. -/
theorem Obs.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : Obs D Γ r info origin n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ origin n Δ S)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    LowerTypeDemand D Γ origin o n Δ out := by
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
  | payload HP =>
    simpa only [LowerTypeDemand, NativeGroundDemand] using
      HP.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee RN
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
    have HI : LowerTypeDemand D Γ origin (.app keys o) n (proofEraseCtx Γ')
        (proofErase Γ' (.forallE A₀ C')) := by
      rw [EP]
      simp only [LowerTypeDemand, NativeGroundDemand]
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
    have HY' := HY.subst (fun W HT H => H.substitute W HT) WI HF.cons
    have hBI := hB.instN henv.ordered Ctx.InstN.zero hxA
    have EI : proofErase Γ' (B'.inst x) = Y.inst a := by
      rw [proofErase_instN hΓA hxA Ctx.InstN.zero hB, EB, Ex]
    have HI : LowerTypeDemand D Γ origin o n (proofEraseCtx Γ') (proofErase Γ' (B'.inst x)) := by
      simpa only [EI, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HY'
    apply HI.compute_type heq hs hΓ hΓ' W hBI
    simpa only [EI] using RC

end ConstructorControlObservation
end Lean4Lean.VEnv.Strengthening
