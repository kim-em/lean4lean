import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaClassification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Function eta survives independent ordinary erased computations

Confluence aligns the independently computed opened bodies. The resulting
contextual eta guard retains the exact sort of the computed annotation. All
finite reductions are allowed, including beta that destroys the displayed eta
shape and computation inside binder annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
namespace ErasedCore

/-- Ordinary erased primitives have computational, rather than lambda, roots. -/
theorem root (H : Step a b) : ProofShape.ComputationalRoot a :=
  erased_compared_K_stage_root 0 H

/-- A typed domain keeps its exact sort after arbitrary ordinary computation. -/
theorem domainSort (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (R : ProofShape.Compute Step (proofErase Γ A) out) :
    ProofShape.DomainSort (proofEraseCtx Γ) out u := by
  obtain ⟨A', _, hA', rfl⟩ := replay hΓ hA R
  exact .of_typed hΓ hA'

/-- A common-reduct certificate between a typed lambda body and an opened
non-proof function survives independent finite computations of the whole lambda
and short function. The residual certificate uses recursive contextual eta. -/
theorem eta_join_shape_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b C)
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (HB : ProofShape.Compute Step (proofErase (A :: Γ) b) shared)
    (HF : ProofShape.Compute Step
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u)) shared)
    (RL : ProofShape.Compute Step (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨A', body', rfl, RA, RB⟩ := RL.lam_inv (fun H => root H)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  have RS : ProofShape.Compute Step
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u))
      (.app (right.liftN 1) (ProofShape.etaArgument u)) :=
    .app (RF.liftN (fun H => erased_iota_primitive_liftN H)) .refl
  obtain ⟨out, HL, HR⟩ := join_forward hcon hΓA hb hopen HB
    (E.symm ▸ HF) RB (E.symm ▸ RS)
  exact .etaBodyL (domainSort hΓ hA RA) (.compute HL HR .refl)

/-- Every pair of ordinary reducts of a canonical non-proof function eta pair
has a contextual common-mode certificate; neither path needs to preserve the
syntactic eta pattern. -/
theorem eta_shape_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (RL : ProofShape.Compute Step
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u))) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  exact eta_join_shape_forward hcon hΓ hA hopen hf hn .refl
    (E ▸ ProofShape.Compute.refl) (E.symm ▸ RL) RF

/-- Actual original function eta remains contextually comparable after arbitrary
independent ordinary erased computation, including whole-proof collapse. -/
theorem eta_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RL : ProofShape.Compute Step (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true left right := by
  classical
  by_cases hp : IsProof Γ f
  · have hpl := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    rw [proofErase_eq_proof.2 hp] at RF
    rw [proofErase_eq_proof.2 hpl] at RL
    have HN : ProofShape.NormalSyntax Step .proof :=
      ⟨fun _ H => (root H).elim, trivial⟩
    obtain rfl := HN.fixed RL
    obtain rfl := HN.fixed RF
    exact .refl
  · have hnl := mt (isProof_congr hΓ (IsDefEq.eta hf)).1 hp
    rw [show proofErase Γ (.lam A (.app f.lift (.bvar 0))) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) (.app f.lift (.bvar 0))) from if_neg hnl,
      proofErase_eta_body hΓ hA hf hp] at RL
    exact eta_shape_forward hcon hΓ hA hf hp RL RF

/-- Any displayed eta guard between common-typed originals survives independent
ordinary computation. Typed classification recovers the canonical eta argument,
so the theorem covers both raw head-eta constructors without extra hypotheses. -/
theorem eta_head_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f))
    (RE : ProofShape.Compute Step (proofErase Γ e) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨A, B, u, hA, hfPi, hn, E⟩ := proofErase_eta_head_classified hΓ he hf H
  exact eta_shape_forward hcon hΓ hA hfPi hn (E ▸ RE) RF

/-- Guards formed by arbitrary ordinary computation followed by displayed eta
also survive independent computation of their common-typed source endpoints.
The two confluence joins retain typed representatives of both eta endpoints. -/
theorem head_eta_join_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (hf : env.HasType univs Γ f T)
    (HE : ProofShape.Compute Step (proofErase Γ e) etaLeft)
    (HF : ProofShape.Compute Step (proofErase Γ f) etaRight)
    (H : ProofShape.EtaHead etaLeft etaRight)
    (RE : ProofShape.Compute Step (proofErase Γ e) left)
    (RF : ProofShape.Compute Step (proofErase Γ f) right) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨left', RL, EL⟩ := confluent hcon hΓ he RE HE
  obtain ⟨right', RR, ER⟩ := confluent hcon hΓ hf RF HF
  obtain ⟨e₀, _, he₀, rfl⟩ := replay hΓ he HE
  obtain ⟨f₀, _, hf₀, rfl⟩ := replay hΓ hf HF
  exact .compute RL RR (eta_head_forward hcon hΓ he₀ hf₀ H EL ER)

end ErasedCore
end Lean4Lean.VEnv.Strengthening
