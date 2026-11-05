import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCallerEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDependentCarrierBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaSquares

/-! # Put native recovery conversions into identity annotations

A recovered type can be made syntax-directed by computing to a beta-cover of
the source. Conversions become computations of written identity annotations.
The cover contracts back to the original source; this is forward construction
from an existing native certificate, not arbitrary assigned-type coverage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

omit [Params] in
/-- A context-independent primitive language permits any ambient scope. -/
theorem unscoped_compute_rescope (R : ScopedCompute (fun _ => Base) Δ a b) :
    ScopedCompute (fun _ => Base) Δ' a b := by
  induction R generalizing Δ' with
  | base H => exact .base H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Base recovery pulls back along pointwise beta reduction of context entries.
The expression and recovered output stay exact. No context interpretation is
needed because the base primitive relation is independent of scope. -/
theorem base_recovery_backward_oracle
    (R : ScopedTypeRecovery (fun _ => Base) Δ e T)
    (W : ∀ i, BetaRed (contextOracle Δ' i) (contextOracle Δ i)) :
    ScopedTypeRecovery (fun _ => Base) Δ' e T := by
  induction R generalizing Δ' with
  | bvar => exact ScopedTypeRecovery.bvar.convert (.beta (W _))
  | sort h => exact .sort h
  | const hc hw hl => exact .const hc hw hl
  | app _ ih => exact .app (ih W)
  | lam _ ih =>
    apply ScopedTypeRecovery.lam
    apply ih
    intro i
    cases i with
    | zero => exact .refl
    | succ i => exact (W i).liftN
  | forallE _ _ ihA ihB =>
    apply ScopedTypeRecovery.forallE (ihA W)
    apply ihB
    intro i
    cases i with
    | zero => exact .refl
    | succ i => exact (W i).liftN
  | proj hi HT hj hl _ ih => exact .proj hi HT hj hl (ih W)
  | convert _ RC ih => exact (ih W).convert (unscoped_compute_rescope RC)

/-- Any native certificate has a forward-computed cover with base recovery at
its exact selected type, provided its conversion paths can run in Target and
Target admits identity expansion using base recovery. The cover beta-reduces
to the original source. All constructors, including dependent products and
projection recipes, are covered; no ordinary type-conversion join is assumed. -/
theorem native_guard_materialize
    (hcompute : ∀ {Δ a b}, ScopedCompute Source Δ a b → ScopedCompute Target Δ a b)
    (hid : ∀ {Δ a A}, ScopedTypeRecovery (fun _ => Base) Δ a A →
      ScopedCompute Target Δ a (.app (.lam A (.bvar 0)) a))
    (R : ScopedTypeRecovery Source Δ e T) :
    ∃ covered, ScopedCompute Target Δ e covered ∧ BetaRed covered e ∧
      ScopedTypeRecovery (fun _ => Base) Δ covered T := by
  induction R with
  | bvar => exact ⟨_, .refl, .refl, .bvar⟩
  | sort h => exact ⟨_, .refl, .refl, .sort h⟩
  | const hc hw hl => exact ⟨_, .refl, .refl, .const hc hw hl⟩
  | app _ ih =>
    obtain ⟨f', RF, BF, NF⟩ := ih
    exact ⟨_, .app RF .refl, .app BF .refl, .app NF⟩
  | lam _ ih =>
    obtain ⟨b', RB, BB, NB⟩ := ih
    exact ⟨_, .lam .refl RB, .lam .refl BB, .lam NB⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A', RA, BA, NA⟩ := ihA
    obtain ⟨B', RB, BB, NB⟩ := ihB
    have NB' := base_recovery_backward_oracle NB (Δ' := A' :: _) (fun i => by
      cases i with
      | zero => exact BA.liftN
      | succ i => exact .refl)
    exact ⟨_, .forallE RA RB, .forallE BA BB, .forallE NA NB'⟩
  | proj hi HT hj hl _ ih =>
    obtain ⟨m', RM, BM, NM⟩ := ih
    exact ⟨_, .proj RM, .proj BM,
      (ScopedTypeRecovery.proj hi HT hj hl NM).convert
        (.beta (projectionType_beta (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) BM))⟩
  | @convert Δ e A B RN RC ih =>
    obtain ⟨covered, Rcover, Bcover, Ncover⟩ := ih
    have RN : ScopedTypeRecovery (fun _ => Base) Δ (.app (.lam B (.bvar 0)) covered) B := by
      have H : ScopedTypeRecovery (fun _ => Base) Δ
          (.app (.lam B (.bvar 0)) covered) ((B.liftN 1).inst covered) := .app (.lam .bvar)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using H
    have RB : BetaRed (.app (.lam B (.bvar 0)) covered) covered := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
        ProofShape.Subst.one, ProofShape.Subst.cons] using
        (BetaRed.beta (A := B) (b := .bvar 0) (a := covered))
    exact ⟨_, Rcover.trans ((hid Ncover).trans (.app (.lam (hcompute RC) .refl) .refl)),
      RB.trans Bcover, RN⟩

/-- If Source computations already simulate in stage one, every Source native
guard can be materialized at stage zero by a stage-one forward path. This is a
conditional simulation tool, not a claim that all higher stages have collapsed. -/
theorem first_stage_native_guard_materialize
    (hcompute : ∀ {Δ a b}, ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : ScopedTypeRecovery Source Δ e T) :
    ∃ covered, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ e covered ∧
      BetaRed covered e ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ covered T := by
  exact native_guard_materialize hcompute
    (Base := fun a b => ErasedStaticStructureEtaExpansionStage D 0 [] a b)
    (fun H => .base (.inr (.inr (.inr (.inl (.intro H)))))) R

/-- Native identity introduces no new stage beyond simulation of the guard's
computations: materialize the source, expand at stage zero, then beta-contract
the cover inside the resulting identity application. -/
theorem first_stage_native_identity_simulation
    (hcompute : ∀ {Δ a b}, ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeIdentityExpansion Source Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro RN =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize hcompute RN
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inl (.intro NC)))))).trans
      (.beta (.app .refl BC)))

/-- Function eta likewise needs no additional stage once guard computations
simulate in stage one. The selected domain is exact and the original source is
restored inside the eta body by beta; no guard transfer across beta is used. -/
theorem first_stage_native_eta_simulation
    (hcompute : ∀ {Δ a b}, ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeEtaExpansion Source Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro RN SD =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize hcompute RN
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inr (.inl (.intro NC SD))))))).trans
      (.beta (.lam .refl (.app BC.liftN .refl))))

/-- Masked structure eta can also use a materialized stage-zero guard. Beta
cleanup restores the original major in every retained field, while erased
proof fields and the complete parameter spine remain unchanged. -/
theorem first_stage_native_structure_simulation
    (hcompute : ∀ {Δ a b}, ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeMaskedStructureExpansion Source Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro hi hx ha hp RN =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize hcompute RN
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inr (.inr (.intro hi hx ha hp NC))))))).trans
      (nativeStructureOutput_compute (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) (.beta BC)))

/-- Unconditionally, a native certificate using stage n computes at stage n+1
to a beta-cover with stage-zero recovery of exactly the same selected type.
This records a concrete cost for materializing all native constructors. -/
theorem staged_native_guard_materialize
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ e T) :
    ∃ covered, ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ e covered ∧
      BetaRed covered e ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ covered T := by
  apply native_guard_materialize
    (Base := fun a b => ErasedStaticStructureEtaExpansionStage D 0 [] a b)
    (fun H => H.mono (erased_static_structure_eta_expansion_stage_mono (Nat.le_succ n))) ?_ R
  intro Δ a A H
  exact .base (.inr (.inr (.inr (.inl (.intro
    (H.mono (erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n))))))))

/-- Every full-union native certificate has a forward-computed beta-cover with
stage-zero recovery at its exact selected type. This does not start from mere
ordinary typing and does not recover that type at the beta-contracted source. -/
theorem union_native_guard_materialize
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e T) :
    ∃ covered, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e covered ∧
      BetaRed covered e ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ covered T := by
  exact native_guard_materialize (fun H => H)
    (Base := fun a b => ErasedStaticStructureEtaExpansionStage D 0 [] a b)
    (fun H => .base ⟨1, .inr (.inr (.inr (.inl (.intro H))))⟩) R

end Lean4Lean.VEnv.Strengthening
