import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandInput
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordInput

/-! # Canonical family joins from finitely observed type aliases

Actual carrier equality fixes the exposed universe instance before raw
substitution. Stored delta cleanup and the target's declared unit-arrow domain
then give one canonical family application. This concerns type computations;
arbitrary term/native histories still require integration with the joint observer.
-/
namespace Lean4Lean.VEnv.Strengthening.AliasDemandProfile
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- Ordinary carrier equality fixes the monomorphic family instance in the
computational readout. Alias unfolding remains an explicit operational step. -/
theorem family_head
    (HE : TypeEquality Δ e (.atom RT))
    (HR : Obs t 1 Δ (fun _ _ _ => False) e .sort .pi) :
    ∃ a, Compute (ErasedIotaPrimitive D₀) (e.subst σ) (.app (.const t []) a) := by
  have HS : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  obtain ⟨ls, args, hn, RB⟩ := HR.head_readout (σ := Subst.id)
  simp only [ProofShape.subst_id] at RB
  obtain ⟨Γ, A, hΓ, _, HE, EA⟩ := HE
  obtain ⟨actual, RA, EE⟩ := proofErase_compute_replay HS (erased_iota_replay HS)
    hΓ HE.hasType.1 (EA ▸ RB)
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EE
  have HE' := HE.symm.trans (RA.simAt HS hΓ _ HE.hasType.1)
  have HF : env.IsDefEqU univs Γ (VExpr.mkApps (.const t []) [Q.value hi hS])
      (VExpr.mkApps (.const t ls) args') := HE'.toU
  have HL := (HF.structApp_inv henv hΓ hTag HE.hasType.2).1
  cases HL
  cases args with
  | nil => simp at hn
  | cons a args =>
    have E : args = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hn; omega)
    subst args
    exact ⟨a.subst σ, by simpa only [ProofShape.mkApps, List.foldl_cons, List.foldl_nil,
      ProofShape.subst] using RB.subst (fun H => erased_iota_primitive_subst H) (σ := σ)⟩

/-- After arbitrary type computation and raw substitution, the actual target
family header canonicalizes the exposed argument. No native certificate for
that argument, substitution interpretation, or normalization premise is used. -/
theorem family_computation_return
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (HE : TypeEquality Δ e (.atom RT))
    (HR : Obs t 1 Δ (fun _ _ _ => False) e .sort .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ e out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
      (out.subst σ) (.app (.const t []) (Q.canonical s uc)) := by
  have HS : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  have HE' := HE.compute (erased_static_structure_eta_expansion_union_descent heq HS) R
  have HR' := HR.static_structure_union heq hcon (henv.projectionRigid hTag) R (fun _ _ _ h => h.elim)
  obtain ⟨a, RB⟩ := family_head hi hS Q hTag hF (σ := σ) HE' HR'
  have RN := Q.stored_family_native (D := D₀) hi hS hΓ hcf hU hT
  have HC := Q.caller_telescope (D := D₀) hi hS heq HS hΓ
    (B := proofErase ((Q.control U).expr :: Γ) B) CallerCanonicalTelescope.nil
  exact (RB.scoped (fun R => .base ⟨0, .inl (.inl R)⟩)).trans
    (HC.compute RN (args := [a]) (by simp))

/-- Independently computed type annotations with the same ordinary carrier
and finite family evidence meet after unrelated raw substitutions. The target
context and all native telescope evidence come from the actual declarations. -/
theorem family_computations_join
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (HE : TypeEquality Δ e (.atom RT))
    (HR : Obs t 1 Δ (fun _ _ _ => False) e .sort .pi)
    (HE' : TypeEquality Δ' e' (.atom RT))
    (HR' : Obs t 1 Δ' (fun _ _ _ => False) e' .sort .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ e out)
    (R' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ' e' out') :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
        (out.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
        (out'.subst τ) (.app (.const t []) (Q.canonical s uc)) :=
  ⟨family_computation_return hi hS Q hTag hF heq hcon hΓ hcf hU hT HE HR R,
    family_computation_return hi hS Q hTag hF heq hcon hΓ hcf hU hT HE' HR' R'⟩

/-- An actual stored alias for a typed family initializes both independent
operational evidence and ordinary carrier equality, with no observation premise. -/
theorem stored_family_evidence
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (HD : (D₀).unfolds name [] (.app (.const t []) p)) :
    TypeEquality (proofEraseCtx Γ) (proofErase Γ (.const name [])) (.atom RT) ∧
      Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
        (proofErase Γ (.const name [])) .sort .pi := by
  have HS : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  have hfamily := (hF.weak0 (Γ := Γ) henv.ordered).app hp
  have HA := (HS Γ name [] _ HD).of_r henv hΓ hfamily
  have HE := IsDefEq.appDF (hF.weak0 (Γ := Γ) henv.ordered) (Q.value_equal hi hS hp)
  exact ⟨⟨Γ, _, hΓ, rfl, HA.trans HE, rfl⟩,
    (Obs.of_rigid (DependentRecordDemand.rigid_family_observation hi hS Q hF hΓ hp)).stored_alias HD hΓ hfamily⟩

include hTag hF in
/-- Concrete alias return discharges all source observation and target native
premises using actual stored declarations and ordinary parameter typing. -/
theorem stored_family_computation_return
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (HD : (D₀).unfolds name [] (.app (.const t []) p))
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
      (proofErase Γ (.const name [])) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
      (out.subst σ) (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HE, HR⟩ := stored_family_evidence hi hS Q hTag hF hΓ hp HD
  exact family_computation_return hi hS Q hTag hF heq hcon hΓ' hcf hU hT HE HR R

end Lean4Lean.VEnv.Strengthening.AliasDemandProfile
