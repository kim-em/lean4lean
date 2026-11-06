import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedWrappers
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpineCutReadout

/-! # Minimal computations force a guarded original-spine cut

Counts turn administrative wrapper bypass into a strict improvement. A path
with minimal outer primitive count therefore reaches either a specialized Eq
guard that reads the lower equation, or a general singleton/function-eta root.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-- The complete spine cut accounts for its selected root: prefix cost plus
one plus tail cost is bounded by the original computation cost. Argument
origins are retained separately and are not counted a second time. -/
theorem ScopedComputeCount.const_spine_or_cut
    (hgood : SpineRootLevels Good c)
    (R : ScopedComputeCount Step cost Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ ls' args', out = ProofShape.mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (ScopedCompute Step Δ) args args') ∨
    (∃ ls' pre pending target cp ct, cp+1+ct ≤ cost ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute Step Δ) args (pre ++ pending) ∧
      ScopedComputeCount Step cp Δ (ProofShape.mkApps (.const c ls) args)
        (ProofShape.mkApps (.const c ls') (pre ++ pending)) ∧
      Step Δ (ProofShape.mkApps (.const c ls') pre) target ∧
      ¬ Good Δ (ProofShape.mkApps (.const c ls') pre) target ∧
      ScopedComputeCount Step ct Δ (ProofShape.mkApps target pending) out) := by
  classical
  generalize E : ProofShape.mkApps (.const c ls) args = source at R
  induction R generalizing ls args with
  | @base Δ₀ source out₀ H =>
    cases E
    by_cases HG : Good Δ₀ (ProofShape.mkApps (.const c ls) args) out₀
    · obtain ⟨ls', EO, HL⟩ := hgood HG
      exact .inl ⟨ls', args, EO, HL, .rfl (fun _ _ => .refl)⟩
    · refine .inr ⟨ls, args, [], _, 0, 0, by omega, .rfl (fun _ _ => by rfl), ?_, ?_, H, HG, .beta .refl⟩
      · simpa only [List.append_nil] using
          (show List.Forall₂ (ScopedCompute Step Δ₀) args args from .rfl (fun _ _ => .refl))
      · simp only [List.append_nil]; exact .beta .refl
  | beta H =>
    cases E
    obtain ⟨args', EO, HA⟩ := H.const_spine
    exact .inl ⟨ls, args', EO, .rfl (fun _ _ => by rfl), HA.imp (fun _ _ H => .beta H)⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨ls₁, args₁, rfl, HL₁, HA₁⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · rcases ih₂ rfl with ⟨ls₂, args₂, EO, HL₂, HA₂⟩ |
        ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
      · exact .inl ⟨ls₂, args₂, EO, HL₁.trans (fun _ _ _ H K => H.trans K) HL₂,
          HA₁.trans (fun _ _ _ H K => H.trans K) HA₂⟩
      · exact .inr ⟨ls', pre, pending, target, _, ct, by omega,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL,
          HA₁.trans (fun _ _ _ H K => H.trans K) HA, R₁.trans RP, H, HN, RT⟩
    · exact .inr ⟨ls', pre, pending, target, cp, _, by omega, HL, HA, RP, H, HN, RT.trans R₂⟩
  | @app c₁ Δ f f' c₂ x x' RF RX ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    rcases ihf rfl with ⟨ls', args', rfl, HL, HA⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · exact .inl ⟨ls', args' ++ [x'], mkApps_snoc.symm, HL, HA.append' (.cons RX.forget .nil)⟩
    · refine .inr ⟨ls', pre, pending ++ [x], target, cp, ct+c₂, by omega, HL, ?_, ?_, H, HN, ?_⟩
      · simpa only [List.append_assoc] using HA.append' (.cons (ScopedCompute.refl (e := x)) .nil)
      · simpa only [← List.append_assoc, mkApps_snoc, Nat.add_zero] using
          ScopedComputeCount.app RP (ScopedComputeCount.beta (BetaRed.refl (e := x)))
      · simpa only [mkApps_snoc] using ScopedComputeCount.app RT RX
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

/-- Every finite computation admits a certificate with minimum outer
primitive count. This uses well-ordering of natural numbers, not normalization. -/
theorem ScopedCompute.minimal_count (R : ScopedCompute Step Δ source out) :
    ∃ cost, ScopedComputeCount Step cost Δ source out ∧
      ∀ k, ScopedComputeCount Step k Δ source out → cost ≤ k := by
  classical
  obtain ⟨cost, RC⟩ := R.count
  have H : ∀ cost, ScopedComputeCount Step cost Δ source out →
      ∃ m, ScopedComputeCount Step m Δ source out ∧
        ∀ k, ScopedComputeCount Step k Δ source out → m ≤ k := by
    intro cost
    induction cost using Nat.strongRecOn with
    | ind cost ih =>
      intro RC
      by_cases hx : ∃ k, k < cost ∧ ScopedComputeCount Step k Δ source out
      · obtain ⟨k, hk, RK⟩ := hx
        exact ih k hk RK
      · refine ⟨cost, RC, ?_⟩
        intro k RK
        by_contra hn
        exact hx ⟨k, by omega, RK⟩
  exact H cost RC

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- A whole probe-exposure path either reads the original lower equality,
or yields an earlier general-singleton/function-eta root on the original spine.
All component origins and both complete path segments are retained. Choosing a
minimum-count path excludes constant and identity expansion cuts by strict
bypass; universe conversion, ordinary core and structure eta are also excluded.
Decoding the two remaining guarded families is not asserted. -/
theorem pi_inert_eq_exposure_readout_or_guarded_spine_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Eargs : args = [(proofErase Γ A).liftN count offset,
      (proofErase Γ a).liftN count offset, M, m, (proofErase Γ b).liftN count offset, .proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    (ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) ∧ env.IsDefEq univs Γ a b A) ∨
    (∃ ls pre pending target,
      List.Forall₂ (· ≈ ·) [v,w] ls ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      PiInertStage D n (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
      (∃ k, k < n ∧
        (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k)
          (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∨
         NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k)
          (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target)) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ') (ProofShape.mkApps target pending) out) := by
  classical
  obtain ⟨cost, RC, hmin⟩ := R.minimal_count
  rcases RC.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args', EO, _, _⟩ | ⟨ls, pre, pending, target, cp, ct, hcost, HL, HA, RP, H, HN, RT⟩
  · exact ((carrier_exposure_ne_eqRec heq HE) (by rw [EO, constHead_mkApps]; rfl)).elim
  · have HA₆ := Eargs ▸ HA
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D n) (ErasedStaticStructureEtaExpansionStage D n) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs n
    by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target
    · have HG := HQ.spine_component_guard (HA₆.imp (fun _ _ R => R.mono pi_inert_stage_embed))
      have HGl := proofErase_computed_joint_carrier_certificate_descend hd hΓ hΓ' W ha hb HG
      exact .inl ⟨HGl, proofErase_computed_joint_carrier_reflect hd.descent hΓ ha hb HGl⟩
    · have HC : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
        rintro (HC | HC)
        · exact pi_inert_eq_prefix_no_core_root hreg hoff hRec HA₆ HC
        · exact HN HC
      have hp : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
      have HTsrc : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
        obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HT
        exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
      have HS := HT.compute hp RP.forget
      rw [ProofShape.mkApps_append] at HS
      have HTpre := RP.forget.spine_cut_source_typed hp HTsrc
      have hbypass : ∀ {Recovery},
          (ConstantExpansion (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∨
           NativeIdentityExpansion Recovery (proofEraseCtx Γ')
             (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) → False := by
        intro Recovery HX
        obtain ⟨k, hk, RB⟩ := pi_inert_expansion_prefix_count_bypass heq hs HTpre HX RT HE
        have RB' : ScopedComputeCount (PiInertStage D n) (cp+k) (proofEraseCtx Γ')
            (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out :=
          RP.trans (by simpa only [ProofShape.mkApps_append] using RB)
        have HM := hmin _ RB'
        omega
      have HR : ∃ k, k < n ∧
          (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k)
            (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∨
           NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k)
            (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) := by
        rcases static_other_spine_root H.1 HC HQ
            (fun H => HS.no_masked_structure_spine hd.descent H) with HC | ⟨k, hk, HC | HI | HEta⟩
        · exact (hbypass (Recovery := ErasedStaticStructureEtaExpansionStage D n) (.inl HC)).elim
        · exact ⟨k, hk, .inl HC⟩
        · exact (hbypass (.inr HI)).elim
        · exact ⟨k, hk, .inr HEta⟩
      exact .inr ⟨ls, pre, pending, target, HL, HA, RP.forget, HTpre, H, HR, RT.forget⟩

end Lean4Lean.VEnv.Strengthening
