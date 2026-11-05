import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedBinderTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Computational injectivity of dependent function types

Type-fork joining and Pi-origin readout extract computational component paths
from a chain between Pi types. Codomain chains are transported to the original
binder context; exact forward transport of native guards is not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Pi types related by a typed computation chain have domain and codomain
chains. The codomain comparison lives under the left domain. Type-fork joining
is an explicit open premise; ordinary Pi injectivity supplies typing only. -/
theorem TypedComputationEq.forallE_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ (.forallE A B) (.forallE A' B') T) :
    (∃ u, TypedComputationEq D Γ A A' (.sort u)) ∧
      ∃ v, TypedComputationEq D (A :: Γ) B B' (.sort v) := by
  obtain ⟨⟨u, HA⟩, v, HB⟩ := IsDefEqU.forallE_inv henv hΓ ⟨_, H.defeq⟩
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.1⟩
  have hΓA' : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.2⟩
  have W : IsDefEqCtx env univs Γ (A :: Γ) (A' :: Γ) := .succ .zero HA
  have hB' := HB.hasType.2.defeqDFC henv W
  have hPi := HasType.forallE HA.hasType.1 HB.hasType.1
  have hPi' := HasType.forallE HA.hasType.2 hB'
  have H' := H.at_source_type hΓ hPi
  obtain ⟨shared, RL, RR⟩ := H'.type_join heq hs HF hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ hPi)] at RL
  rw [show proofErase Γ (.forallE A' B') = .forallE (proofErase Γ A') (proofErase (A' :: Γ) B') from
    if_neg (not_isProof_of_sort hΓ hPi')] at RR
  obtain ⟨X, Y, OL, Rβ⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ
    HA.hasType.1 HB.hasType.1 RL
  have OR := proofErase_static_structure_union_pi_components heq hs hΓ
    HA.hasType.2 hB' (RR.trans (.beta Rβ))
  obtain ⟨_, _, _, _, _, _, RAL, RBL⟩ := OL
  obtain ⟨_, _, _, _, _, _, RAR, RBR⟩ := OR
  have HAc := TypedComputationEq.of_join heq hs hΓ HA.hasType.1 HA.hasType.2 RAL RAR
  obtain ⟨b, HL, EL⟩ := TypedComputationEq.realize_compute heq hs hΓA HB.hasType.1 RBL
  obtain ⟨b', HR, ER⟩ := TypedComputationEq.realize_compute heq hs hΓA' hB' RBR
  have HR' := HR.defeqCtx heq hs hΓ (W.symm henv.ordered)
  have E : proofErase (A :: Γ) b = proofErase (A :: Γ) b' := by
    rw [proofErase_defeqCtx hΓA W HR'.defeq.hasType.2]
    exact EL.trans ER.symm
  have HM := TypedComputationEq.of_erasure_eq (D := D) ((HL.defeq.symm.trans HB).trans HR'.defeq) E
  exact ⟨⟨u, HAc⟩, v, HL.trans (HM.trans HR'.symm)⟩

end Lean4Lean.VEnv.Strengthening
