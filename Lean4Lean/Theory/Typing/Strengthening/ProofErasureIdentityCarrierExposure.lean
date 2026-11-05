import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqComputedFunctionCarrierSimulation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutHistory

/-! # Carrier exposure with written endpoint annotations

Identity wrappers retain the selected carrier while their payloads compute.
Function exposure passes an identity wrapper to its recursive body, rather
than asking an unannotated endpoint for native recovery after computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Stage-one exposure starts with explicit identity annotations on both
endpoints. The carrier and endpoint outputs have a stage-zero carrier guard.
This is an interface, not a claim that every comparison has such exposure. -/
def IdentityCarrierExposure (D : Definitions) (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  ∃ C x y, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ A C ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) a) x ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) b) y ∧
    ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) Δ C x y

/-- A base guard needs only beta contraction of the two identity annotations. -/
theorem IdentityCarrierExposure.of_guard
    (H : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) Δ A a b) :
    IdentityCarrierExposure D Δ A a b :=
  ⟨_, _, _, .refl, .beta (raw_identity_beta _ _), .beta (raw_identity_beta _ _), H⟩

/-- Endpoint computations run inside retained identity annotations. The
recursive exposure consequently starts with exactly its required wrappers. -/
theorem IdentityCarrierExposure.reduce
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ b b')
    (H : IdentityCarrierExposure D Δ A a' b') : IdentityCarrierExposure D Δ A a b := by
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  exact ⟨C, x, y, RC, (ScopedCompute.app .refl Ra).trans RX,
    (ScopedCompute.app .refl Rb).trans RY, HG⟩

/-- Carrier computation updates both written identity annotations before
recursive exposure. No native certificate is transferred across a beta step. -/
theorem IdentityCarrierExposure.carrier_compute
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ A A')
    (H : IdentityCarrierExposure D Δ A' a b) : IdentityCarrierExposure D Δ A a b := by
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  exact ⟨C, x, y, R.trans RC, (ScopedCompute.app (.lam R .refl) .refl).trans RX,
    (ScopedCompute.app (.lam R .refl) .refl).trans RY, HG⟩

/-- Symmetry only exchanges the endpoint paths and reverses the final guard. -/
theorem IdentityCarrierExposure.symm (H : IdentityCarrierExposure D Δ A a b) :
    IdentityCarrierExposure D Δ A b a := by
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  exact ⟨C, y, x, RC, RY, RX, .carrierSymm HG⟩

/-- Exposure can retain one additional identity layer at the computed carrier.
Both outputs then recover that carrier at stage zero and compare at stage zero
in either mode. This turns a recursive carrier result into a comparison of
annotated outputs without discarding its computable type history. -/
theorem IdentityCarrierExposure.native_compared_outputs
    (H : IdentityCarrierExposure D Δ A a b) :
    ∃ C x y, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ A C ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) a) x ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) b) y ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ x C ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ y C ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ mode x y := by
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  have openLeft : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.app (.lam A (.bvar 0)) a) (.app (.lam A (.bvar 0)) (.app (.lam A (.bvar 0)) a)) :=
    .base (.inr (.inr (.inr (.inl (.intro (raw_identity_native _ _))))))
  have openRight : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.app (.lam A (.bvar 0)) b) (.app (.lam A (.bvar 0)) (.app (.lam A (.bvar 0)) b)) :=
    .base (.inr (.inr (.inr (.inl (.intro (raw_identity_native _ _))))))
  exact ⟨C, _, _, RC, openLeft.trans (.app (.lam RC .refl) RX),
    openRight.trans (.app (.lam RC .refl) RY), raw_identity_native _ _, raw_identity_native _ _,
    .appCarrier (.lam .bvar) (.leaf .refl) HG⟩

/-- A function identity wrapper opens to a lambda whose body retains its own
codomain annotation. The raw payload is unrestricted; domain and codomain
typings supply the exact eta/beta restoration law. -/
theorem first_stage_identity_function_body
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (.app (.lam (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.bvar 0)) f)
      (.lam (proofErase Γ A) (.app (.lam (proofErase (A :: Γ) B) (.bvar 0))
        (.app (f.liftN 1) (etaArgument u)))) := by
  let Q := ProofShape.forallE (proofErase Γ A) (proofErase (A :: Γ) B)
  let F := ProofShape.app (.lam Q (.bvar 0)) f
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) F Q :=
    raw_identity_native _ _
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) F
      (.lam (proofErase Γ A) (.app (F.liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN (DomainSort.of_typed hΓ hA)))))))
  have RNL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofErase Γ A :: proofEraseCtx Γ) (F.liftN 1)
      (.forallE ((proofErase Γ A).liftN 1) ((proofErase (A :: Γ) B).liftN 1 1)) := by
    simpa only [F, Q, ProofShape.liftN, liftVar, Nat.reduceAdd, Nat.zero_lt_one, ↓reduceIte] using
      (raw_identity_native (Step := ErasedStaticStructureEtaExpansionStage D 0)
        (Δ := proofErase Γ A :: proofEraseCtx Γ) (Q.liftN 1) (f.liftN 1))
  have RNB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofErase Γ A :: proofEraseCtx Γ) (.app (F.liftN 1) (etaArgument u))
      (proofErase (A :: Γ) B) := by
    simpa only [proofErase_eta_inst hΓ hA hB] using
      (ScopedTypeRecovery.app (a := etaArgument u) RNL)
  have RI : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1)
      (proofErase Γ A :: proofEraseCtx Γ) (.app (F.liftN 1) (etaArgument u))
      (.app (.lam (proofErase (A :: Γ) B) (.bvar 0)) (.app (F.liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inl (.intro RNB)))))
  exact RE.trans (.lam .refl (RI.trans (.beta (.app .refl (.app (raw_identity_beta Q f).liftN .refl)))))

/-- Function exposure is closed under the same identity-annotated invariant
at its recursive body. Typed replay supplies beta restoration of the exposed
bodies, including proof-valued arguments. This closes the recursive function
case without requiring standalone exposure of the unwrapped functions. -/
theorem IdentityCarrierExposure.function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (ha : env.HasType univs Γ a (.forallE A B)) (hb : env.HasType univs Γ b (.forallE A B))
    (H : IdentityCarrierExposure D (proofErase Γ A :: proofEraseCtx Γ) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) (.app a.lift (.bvar 0)))
      (proofErase (A :: Γ) (.app b.lift (.bvar 0)))) :
    IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ a) (proofErase Γ b) := by
  have hQ := HasType.forallE hA hB
  have EQ : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hQ)
  by_cases hpa : IsProof Γ a
  · have hpb := isProof_of_common_type hΓ ha hb hpa
    rw [proofErase_eq_proof.2 hpa, proofErase_eq_proof.2 hpb]
    exact .of_guard (.carrierChecked (.leaf .refl))
  have hpb : ¬ IsProof Γ b := fun H => hpa (isProof_of_common_type hΓ hb ha H)
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  have RPa := first_stage_identity_function_body (D := D) (f := proofErase Γ a) hΓ hA hB
  have RPb := first_stage_identity_function_body (D := D) (f := proofErase Γ b) hΓ hA hB
  rw [proofErase_eta_body hΓ hA ha hpa] at RX
  rw [proofErase_eta_body hΓ hA hb hpb] at RY
  have Ra := RPa.trans (.lam .refl RX)
  have Rb := RPb.trans (.lam .refl RY)
  have hca := (nativeIdentityExpansion_equal ha).hasType.1
  have hcb := (nativeIdentityExpansion_equal hb).hasType.1
  have Eca := proofErase_nativeIdentityExpansion hΓ ha hpa
  have Ecb := proofErase_nativeIdentityExpansion hΓ hb hpb
  have getBeta {f out : ProofShape} {actual : VExpr}
      (hf : env.HasType univs Γ actual (.forallE A B))
      (Ef : proofErase Γ actual = f)
      (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) f
        (.lam (proofErase Γ A) out)) :
      BetaRed (.app ((ProofShape.lam (proofErase Γ A) out).liftN 1) (etaArgument u)) out := by
    obtain ⟨actualOut, HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ hf rfl Ef R
    obtain ⟨L, body, rfl, _, EL, Ebody⟩ := erase_lam_inv EE
    obtain ⟨⟨_, hL⟩, _, hbody⟩ := HE.hasType.2.lam_inv henv hΓ
    have hu := proofErase_sort_levels hΓ hL hA EL
    have hLu := (IsDefEq.sortDF (hL.sort_r henv hΓ) (hA.sort_r henv hΓ) hu).defeq hL
    have EI := proofErase_eta_inst hΓ hLu hbody
    rw [Ebody] at EI
    simpa only [ProofShape.liftN, EI] using
      (BetaRed.beta (A := (proofErase Γ A).liftN 1) (b := out.liftN 1 1) (a := etaArgument u))
  have BA := getBeta hca (Eca.trans (congrArg (fun Q => ProofShape.app (.lam Q (.bvar 0)) (proofErase Γ a)) EQ)) Ra
  have BB := getBeta hcb (Ecb.trans (congrArg (fun Q => ProofShape.app (.lam Q (.bvar 0)) (proofErase Γ b)) EQ)) Rb
  rw [EQ]
  exact ⟨.forallE (proofErase Γ A) C, _, _, .forallE .refl RC, Ra, Rb,
    .carrierFunction (DomainSort.of_typed hΓ hA) (.carrierReduce (.beta BA) (.beta BB) HG)⟩

end Lean4Lean.VEnv.Strengthening
