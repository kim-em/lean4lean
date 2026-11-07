import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorEtaCut

/-! # Preserve the argument budget in constructor readout

Retained argument paths together use no more primitive occurrences than the
original spine computation. This quantitative fact is needed when a selected
field replaces a projection path inside a minimum-count argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
namespace ProofShape

/-- The stable branch of the spine cut retains the total argument cost. The
other branch keeps the same counted root decomposition and argument ancestry. -/
theorem ScopedComputeCount.const_spine_or_cut_budget
    (hgood : SpineRootLevels Good c)
    (R : ScopedComputeCount Step cost Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ ls' args' ca, ca ≤ cost ∧ out = ProofShape.mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ ScopedArgumentsCount Step Δ ca args args') ∨
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
    · obtain ⟨ls', HE, HL⟩ := hgood HG
      exact .inl ⟨ls', args, 0, by omega, HE, HL, .refl⟩
    · refine .inr ⟨ls, args, [], _, 0, 0, by omega, .rfl (fun _ _ => by rfl), ?_, ?_, H, HG, .beta .refl⟩
      · simpa only [List.append_nil] using
          (show List.Forall₂ (ScopedCompute Step Δ₀) args args from .rfl (fun _ _ => .refl))
      · simp only [List.append_nil]; exact .beta .refl
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.const_spine
    exact .inl ⟨ls, args', 0, by omega, HE, .rfl (fun _ _ => by rfl), .beta HA⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨ls₁, args₁, ca₁, hca₁, rfl, HL₁, HA₁⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · rcases ih₂ rfl with ⟨ls₂, args₂, ca₂, hca₂, HE, HL₂, HA₂⟩ |
        ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
      · exact .inl ⟨ls₂, args₂, ca₁+ca₂, by omega, HE,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL₂, HA₁.trans HA₂⟩
      · exact .inr ⟨ls', pre, pending, target, _, ct, by omega,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL,
          HA₁.forget.trans (fun _ _ _ H K => H.trans K) HA, R₁.trans RP, H, HN, RT⟩
    · exact .inr ⟨ls', pre, pending, target, cp, _, by omega, HL, HA, RP, H, HN, RT.trans R₂⟩
  | @app c₁ Δ f f' c₂ x x' RF RX ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    rcases ihf rfl with ⟨ls', args', ca, hca, rfl, HL, HA⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · exact .inl ⟨ls', args' ++ [x'], ca+c₂, by omega, mkApps_snoc.symm, HL,
        by simpa only [Nat.add_zero] using HA.append (.cons RX .nil)⟩
    · refine .inr ⟨ls', pre, pending ++ [x], target, cp, ct+c₂, by omega, HL, ?_, ?_, H, HN, ?_⟩
      · simpa only [List.append_assoc] using HA.append' (.cons (ScopedCompute.refl (e := x)) .nil)
      · simpa only [← List.append_assoc, mkApps_snoc, Nat.add_zero] using
          ScopedComputeCount.app RP (ScopedComputeCount.beta (BetaRed.refl (e := x)))
      · simpa only [mkApps_snoc] using ScopedComputeCount.app RT RX
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

end ProofShape
variable [Params] {D : Definitions}

/-- Exposed rigid-spine readout preserves the argument budget or returns the
actual minimum-count eta cut. The cut's minimum is bounded by the supplied
certificate through its stored minimality property. -/
theorem pi_inert_counted_rigid_spine_readout_or_eta_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (R : ScopedComputeCount (PiInertStage D n) bound Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ levels args' ca, ca ≤ bound ∧ out = ProofShape.mkApps (.const c levels) args' ∧
      List.Forall₂ (· ≈ ·) ls levels ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args args') ∨
    RigidSpineEtaCut D n Δ c ls args out := by
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c := by
    intro Ω levels params target H
    exact erased_level_recovered_stage_spine_levels heq hc hD 0 (Δ := Ω) H
  obtain ⟨cost, RC, Hmin⟩ := R.forget.minimal_count
  have hcost := Hmin _ R
  rcases RC.const_spine_or_cut_budget @hroot with ⟨levels, args', ca, hca, HE, HL, HA⟩ |
      ⟨levels, pre, pending, target, before, after, HB, HL, HA, RP, HR, HN, RT⟩
  · exact .inl ⟨levels, args', ca, by omega, HE, HL, HA⟩
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  have HP := RP.forget.spine_cut_source_typed @hd HT
  have hwrap : ∀ {Recovery},
      (ConstantExpansion (ProofShape.mkApps (.const c levels) pre) target ∨
       NativeIdentityExpansion Recovery Δ (ProofShape.mkApps (.const c levels) pre) target) → False := by
    intro Recovery H
    obtain ⟨j, hj, RJ⟩ := pi_inert_expansion_prefix_count_bypass_nonlambda heq hs HP H RT hout
    rw [← ProofShape.mkApps_append] at RJ
    have HM := Hmin _ (RP.trans RJ)
    omega
  rcases static_structure_rigid_expansion_root heq hc HR.1 (ProofShape.constHead_mkApps _ _) with
    H | H | ⟨k, hk, H | H | H⟩
  · exact (HN H).elim
  · exact (hwrap (Recovery := PiInertStage D n) (.inl H)).elim
  · exact (hwrap (.inr H)).elim
  · exact .inr ⟨cost, levels, pre, pending, target, before, after,
      RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, .inl H⟩
  · exact .inr ⟨cost, levels, pre, pending, target, before, after,
      RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, .inr H⟩

end Lean4Lean.VEnv.Strengthening
