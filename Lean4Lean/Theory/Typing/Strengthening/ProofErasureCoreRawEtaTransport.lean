import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaResidual
import Lean4Lean.Theory.Typing.Strengthening.FreshPatternReflection

/-! # Raw checking transport for typed function eta under core computation

Original fresh-application reflection strengthens the contextual transport result:
the residual is a raw checking certificate, usable by context-independent K
stages. The proof retains typed sources and allows all finite ordinary paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
namespace ErasedCore

private theorem core_sound : definitions.Sound env univs :=
  RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)

/-- A finite ordinary erased path from a typed opened function reflects into a
path of the function itself. The long endpoint needs only displayed eta or
common lambda checking against the reflected function. -/
theorem fresh_application_raw
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ProofShape.Compute Step
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u)) body)
    (D : ProofShape) :
    ∃ f', ProofShape.Compute Step (proofErase Γ f) f' ∧
      ProofShape.EtaResidual (.lam D body) f' := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨out, R0, _, EO⟩ := replay hΓA hopen (E.symm ▸ R)
  obtain ⟨f₀, RF, H⟩ := R0.fresh_application
  have HF := RF.simAt core_sound hΓ _ hf
  have hf₀ := HF.hasType.2
  have hn₀ := mt (isProof_congr hΓ HF).2 hn
  have RR := proofErase_pattern_compute_forward core_sound hcon hΓ hf RF
  refine ⟨proofErase Γ f₀, RR, ?_⟩
  rcases H with rfl | ⟨D₀, rfl⟩
  · have EB := EO.symm.trans (proofErase_eta_body hΓ hA hf₀ hn₀)
    rw [EB]
    classical
    unfold ProofShape.etaArgument
    split
    · exact .eta .proof
    · exact .eta .boundVar
  · obtain ⟨⟨v, hD⟩, _, hb⟩ := hf₀.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := ((HasType.lam hD hb).uniqU henv hΓ hf₀).forallE_inv henv hΓ
    have EB := proofErase_defeqCtx (Γ₁ := D₀ :: Γ) ⟨hΓ, _, hD⟩ (.succ .zero hDA) hb
    rw [show proofErase Γ (.lam D₀ out) =
      .lam (proofErase Γ D₀) (proofErase (D₀ :: Γ) out) from if_neg hn₀,
      EB, EO]
    exact .lam

/-- Recursive eta bodies witnessed by literal common reducts also transport
with raw guards. Computation of the opened short function is reflected back
before the independently computed short endpoint is joined. -/
theorem eta_body_join_raw_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b C)
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (HB : ProofShape.Compute Step (proofErase (A :: Γ) b) shared)
    (HF : ProofShape.Compute Step
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u)) shared)
    (RL : ProofShape.Compute Step (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.RawCheckedCompare Step true left right := by
  obtain ⟨A', body', rfl, _, RB⟩ := RL.lam_inv (fun H => root H)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨body'', RB', RS⟩ := confluent hcon hΓA hb RB HB
  obtain ⟨f', RR, Hη⟩ := fresh_application_raw hcon hΓ hA hf hn (HF.trans RS) A'
  obtain ⟨common, RF', RR'⟩ := confluent hcon hΓ hf RF RR
  obtain ⟨left', RL', Hη'⟩ := Hη.compute_right (fun H => root H)
    (fun H => erased_iota_primitive_liftN H) RR'
  exact .compute ((ProofShape.Compute.lam .refl RB').trans RL') RF' Hη'.rawChecked

/-- Canonical typed eta guards transport through independent arbitrary ordinary
computations on both sides with a raw, rather than merely contextual, result. -/
theorem eta_shape_raw_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (RL : ProofShape.Compute Step
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u))) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.RawCheckedCompare Step true left right := by
  obtain ⟨A', body', rfl, _, RB⟩ := RL.lam_inv (fun H => root H)
  obtain ⟨f', RR, Hη⟩ := fresh_application_raw hcon hΓ hA hf hn RB A'
  obtain ⟨common, RF', RR'⟩ := confluent hcon hΓ hf RF RR
  obtain ⟨left', RL', Hη'⟩ := Hη.compute_right (fun H => root H)
    (fun H => erased_iota_primitive_liftN H) RR'
  exact .compute RL' RF' Hη'.rawChecked

/-- Both raw head-eta constructors at common original types have forward raw
checking transport. Typed classification rules out the unchecked marker case. -/
theorem eta_head_raw_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f))
    (RE : ProofShape.Compute Step (proofErase Γ e) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.RawCheckedCompare Step true left right := by
  obtain ⟨A, B, u, hA, hfPi, hn, E⟩ := proofErase_eta_head_classified hΓ he hf H
  exact eta_shape_raw_forward hcon hΓ hA hfPi hn (E ▸ RE) RF

/-- Earlier computations ending in a displayed eta guard may also be followed
by independent source computations while retaining a raw checking certificate. -/
theorem head_eta_join_raw_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (hf : env.HasType univs Γ f T)
    (HE : ProofShape.Compute Step (proofErase Γ e) etaLeft)
    (HF : ProofShape.Compute Step (proofErase Γ f) etaRight)
    (H : ProofShape.EtaHead etaLeft etaRight)
    (RE : ProofShape.Compute Step (proofErase Γ e) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.RawCheckedCompare Step true left right := by
  obtain ⟨left', RL, EL⟩ := confluent hcon hΓ he RE HE
  obtain ⟨right', RR, ER⟩ := confluent hcon hΓ hf RF HF
  obtain ⟨e₀, _, he₀, rfl⟩ := replay hΓ he HE
  obtain ⟨f₀, _, hf₀, rfl⟩ := replay hΓ hf HF
  exact .compute RL RR (eta_head_raw_forward hcon hΓ he₀ hf₀ H EL ER)

end ErasedCore
end Lean4Lean.VEnv.Strengthening
