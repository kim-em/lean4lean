import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredRecoveryBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierPairedBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure

/-! # Converted function carriers obstruct common beta stability

A neutral family applied to distinct unit variables gives convertible domains
with no common computational result. Variables at function types over these
domains share a positive subsingleton carrier by conversion, but their native
lookup types cannot join. Identity applications therefore compare while their
beta reducts do not, even in the recovered-carrier union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A closed positive empty structure refutes unrestricted common-mode beta
stability of the recovered-carrier union. The source comparison needs only the
base stage; the variable reducts fail comparison at every finite stage. The
obstruction concerns this certificate grammar, not declarative strengthening. -/
theorem carrier_recovered_converted_unit_beta_boundary
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A a b i j, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a A ∧ env.HasType univs Γ b A ∧
      CarrierRecoveredCompare (ErasedCarrierRecoveredStage D 0) (proofEraseCtx Γ) true
        (proofErase Γ a) (proofErase Γ b) ∧
      ProofShape.BetaRed (proofErase Γ a) (proofErase Γ (.bvar i)) ∧
      ProofShape.BetaRed (proofErase Γ b) (proofErase Γ (.bvar j)) ∧
      ¬ CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  let S := VExpr.const family ls
  let F := VExpr.forallE S (.sort (.succ u))
  let Γ₀ := [S, S, F]
  have hu := hS.sort_r henv (show OnCtx ([] : List VExpr) (env.IsType univs) from trivial)
  have hF : env.HasType univs [] F (.sort (.imax (.succ u) (.succ (.succ u)))) :=
    .forallE hS (.sort hu)
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hF⟩, _, hS.weak0 henv.ordered⟩, _, hS.weak0 henv.ordered⟩
  have hS₀ : env.HasType univs Γ₀ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hp₀ : env.HasType univs Γ₀ (.bvar 0) S := .bvar .zero
  have hq₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hf₀ : env.HasType univs Γ₀ (.bvar 2) F := .bvar (.succ (.succ .zero))
  let P := VExpr.app (.bvar 2) (.bvar 0)
  let Q := VExpr.app (.bvar 2) (.bvar 1)
  have hP : env.HasType univs Γ₀ P (.sort (.succ u)) := hf₀.app hp₀
  have hQ : env.HasType univs Γ₀ Q (.sort (.succ u)) := hf₀.app hq₀
  have hpq : env.IsDefEq univs Γ₀ (.bvar 0) (.bvar 1) S :=
    .unitLike (params := []) (levels := ls) hi hp.symm hx hf hp₀ hq₀
  have hPQ : env.IsDefEq univs Γ₀ P Q (.sort (.succ u)) := hf₀.appDF hpq
  let A := VExpr.forallE P S
  let B := VExpr.forallE Q S
  have hA : env.HasType univs Γ₀ A (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hP (hS.weak0 henv.ordered))
  have hB : env.HasType univs Γ₀ B (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hQ (hS.weak0 henv.ordered))
  have hAB := IsDefEq.forallEDF hPQ (hS.weak0 henv.ordered (Γ := P :: Γ₀))
  let Γ := B.lift :: A :: Γ₀
  have hΓA : OnCtx (A :: Γ₀) (env.IsType univs) := ⟨hΓ₀, _, hA⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓA, _, hB.weak henv⟩
  have W : Ctx.LiftN 2 0 Γ₀ Γ := .zero [B.lift, A]
  have hAΓ : env.HasType univs Γ (A.liftN 2) (.sort (.succ u)) := hA.weakN henv W
  have hxΓ : env.HasType univs Γ (.bvar 1) (A.liftN 2) := by
    simpa [A, P, S, Γ, VExpr.lift, VExpr.liftN, liftVar] using
      (HasType.bvar (env := env) (U := univs) (Γ := Γ) (i := 1) (Lookup.succ Lookup.zero))
  have hyB : env.HasType univs Γ (.bvar 0) (B.liftN 2) := by
    simpa [B, Q, S, Γ, VExpr.lift, VExpr.liftN, liftVar] using
      (HasType.bvar (env := env) (U := univs) (Γ := Γ) (i := 0) Lookup.zero)
  have hyΓ : env.HasType univs Γ (.bvar 0) (A.liftN 2) :=
    (hAB.weakN henv W).symm.defeq hyB
  have EP : proofErase Γ₀ P = .app (.bvar 2) (.bvar 0) := by
    rw [show proofErase Γ₀ P = .app _ _ from if_neg (not_isProof_of_sort hΓ₀ hP),
      show proofErase Γ₀ (.bvar 2) = .bvar 2 from
        if_neg (not_isProof_fn hΓ₀ hf₀ hp₀ (not_isProof_of_sort hΓ₀ hP)),
      show proofErase Γ₀ (.bvar 0) = .bvar 0 from
        if_neg (by exact not_proof_at_positive_type hΓ₀ hS₀ hp₀)]
  have EQ : proofErase Γ₀ Q = .app (.bvar 2) (.bvar 1) := by
    rw [show proofErase Γ₀ Q = .app _ _ from if_neg (not_isProof_of_sort hΓ₀ hQ),
      show proofErase Γ₀ (.bvar 2) = .bvar 2 from
        if_neg (not_isProof_fn hΓ₀ hf₀ hq₀ (not_isProof_of_sort hΓ₀ hQ)),
      show proofErase Γ₀ (.bvar 1) = .bvar 1 from
        if_neg (by exact not_proof_at_positive_type hΓ₀ hS₀ hq₀)]
  have hΓP : OnCtx (P :: Γ₀) (env.IsType univs) := ⟨hΓ₀, _, hP⟩
  have hΓQ : OnCtx (Q :: Γ₀) (env.IsType univs) := ⟨hΓ₀, _, hQ⟩
  have EA : proofErase Γ₀ A = .forallE (.app (.bvar 2) (.bvar 0)) (.const family ls) := by
    rw [show proofErase Γ₀ A = .forallE _ _ from if_neg (not_isProof_of_sort hΓ₀ hA), EP,
      show proofErase (P :: Γ₀) S = .const family ls from
        if_neg (not_isProof_of_sort hΓP (hS.weak0 henv.ordered))]
  have EB : proofErase Γ₀ B = .forallE (.app (.bvar 2) (.bvar 1)) (.const family ls) := by
    rw [show proofErase Γ₀ B = .forallE _ _ from if_neg (not_isProof_of_sort hΓ₀ hB), EQ,
      show proofErase (Q :: Γ₀) S = .const family ls from
        if_neg (not_isProof_of_sort hΓQ (hS.weak0 henv.ordered))]
  have EAΓ : proofErase Γ (A.liftN 2) =
      .forallE (.app (.bvar 4) (.bvar 2)) (.const family ls) := by
    rw [proofErase_liftN hΓ₀ hΓ W hA, EA]; rfl
  have EBΓ : proofErase Γ (B.liftN 2) =
      .forallE (.app (.bvar 4) (.bvar 3)) (.const family ls) := by
    rw [proofErase_liftN hΓ₀ hΓ W hB, EB]; rfl
  have Ei : contextOracle (proofEraseCtx Γ) 1 = proofErase Γ (A.liftN 2) := by
    rw [proofEraseCtx_oracle]
    apply erasedTypeOracle_valid hΓ
    simpa [A, P, S, Γ, VExpr.lift, VExpr.liftN, liftVar] using
      (Lookup.succ (Lookup.zero (Γ := Γ₀) (ty := A)) (A := B.lift))
  have Ej : contextOracle (proofEraseCtx Γ) 0 = proofErase Γ (B.liftN 2) := by
    rw [proofEraseCtx_oracle]
    apply erasedTypeOracle_valid hΓ
    simpa [B, Q, S, Γ, VExpr.lift, VExpr.liftN, liftVar] using
      (Lookup.zero (Γ := A :: Γ₀) (ty := B.lift))
  have HN : ¬ ∃ T, ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (contextOracle (proofEraseCtx Γ) 1) T ∧
      ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
        (contextOracle (proofEraseCtx Γ) 0) T := by
    rw [Ei, Ej, EAΓ, EBΓ]
    rintro ⟨T, R, R'⟩
    obtain ⟨_, _, E, RP⟩ := R.forallE_domain_inv erased_carrier_recovered_union_head
    obtain ⟨_, _, E', RQ⟩ := R'.forallE_domain_inv erased_carrier_recovered_union_head
    have HP := RP.bvar_app_fixed erased_carrier_recovered_union_head
    have HQ := RQ.bvar_app_fixed erased_carrier_recovered_union_head
    have HE := (ProofShape.forallE.inj (E.symm.trans E')).1
    rw [HP, HQ] at HE
    cases HE
  have HC : ComputedJointCarrierGuard (ErasedCarrierRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (A.liftN 2)) (proofErase Γ (.bvar 1)) (proofErase Γ (.bvar 0)) := by
    rw [EAΓ]
    exact .carrierSubsingleton (.forallE (.unit hi hx hf (ps := []) hp.symm))
  obtain ⟨a, b, ha, hb, H, RA, RB, Hno⟩ :=
    carrier_recovered_identity_beta_of_unjoined_lookup erased_carrier_recovered_union_head
      hΓ hAΓ hxΓ hyΓ (by decide : 1 ≠ 0) HC HN
  exact ⟨Γ, A.liftN 2, a, b, 1, 0, hΓ, ha, hb, H, RA, RB, Hno⟩

end Lean4Lean.VEnv.Strengthening
