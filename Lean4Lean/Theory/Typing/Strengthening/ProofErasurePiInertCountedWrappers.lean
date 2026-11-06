import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationCount
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantElimination

/-! # Quantitative removal of Pi-inert wrappers

The outer primitive count excludes guard derivations and all beta steps.
Single-rule descent preserves that count below unused binders. Wrapper removal
may discard annotation and argument computations, but must not increase the
remaining count; this is the measure needed to bypass an expansion strictly.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- Pointwise argument computation with the sum of its outer primitive counts. -/
inductive ScopedArgumentsCount (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : Nat → List ProofShape → List ProofShape → Prop where
  | nil : ScopedArgumentsCount Step Δ 0 [] []
  | cons : ScopedComputeCount Step m Δ a b → ScopedArgumentsCount Step Δ n as bs →
      ScopedArgumentsCount Step Δ (m+n) (a :: as) (b :: bs)

/-- Unchanged arguments consume no primitive occurrences. -/
theorem ScopedArgumentsCount.refl : ScopedArgumentsCount Step Δ 0 args args := by
  induction args with
  | nil => exact .nil
  | cons a args ih => exact .cons (.beta .refl) ih

/-- Pointwise beta computation has zero primitive cost. -/
theorem ScopedArgumentsCount.beta (H : List.Forall₂ BetaRed args args') :
    ScopedArgumentsCount Step Δ 0 args args' := by
  induction H with
  | nil => exact .nil
  | cons H _ ih => exact .cons (.beta H) ih

/-- Pointwise composition adds the two argument-vector costs. -/
theorem ScopedArgumentsCount.trans (H : ScopedArgumentsCount Step Δ m args mid)
    (K : ScopedArgumentsCount Step Δ n mid out) : ScopedArgumentsCount Step Δ (m+n) args out := by
  induction H generalizing n out with
  | nil => cases K; exact .nil
  | cons H HS ih =>
    cases K with
    | cons K KS =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ScopedArgumentsCount.cons (H.trans K) (ih KS)

/-- Appending a pending argument vector adds its cost. -/
theorem ScopedArgumentsCount.append (H : ScopedArgumentsCount Step Δ m args args')
    (K : ScopedArgumentsCount Step Δ n rest rest') :
    ScopedArgumentsCount Step Δ (m+n) (args ++ rest) (args' ++ rest') := by
  induction H with
  | nil => simpa only [Nat.zero_add, List.nil_append] using K
  | cons H HS ih =>
    simpa only [Nat.add_assoc, List.cons_append] using ScopedArgumentsCount.cons H ih

/-- A function path and its pointwise argument paths compute the whole spine. -/
theorem ScopedComputeCount.mkApps (HF : ScopedComputeCount Step m Δ f f')
    (HA : ScopedArgumentsCount Step Δ n args args') :
    ScopedComputeCount Step (m+n) Δ (ProofShape.mkApps f args) (ProofShape.mkApps f' args') := by
  induction HA generalizing m f f' with
  | nil => simpa only [Nat.add_zero, ProofShape.mkApps] using HF
  | cons HA HS ih =>
    simpa only [Nat.add_assoc, ProofShape.mkApps] using ih (ScopedComputeCount.app HF HA)

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private lambda_spine_app lambda_spine_lam lambda_spine_not_primitive beta_lambda_spine
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta
variable [Params]

/-- Pi-inert descent reconstructs one lower primitive per upper primitive.
The full-stage root descends once and its source-head restriction reflects. -/
theorem pi_inert_stage_rule_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveRuleDescent (PiInertStage D n) (PiInertStage D n) := by
  intro Γ Γ' count offset e T out hΓ hΓ' W ht H
  obtain ⟨e', HE, HR, EE⟩ := erased_static_structure_eta_expansion_stage_rule_descent
    heq hs n hΓ hΓ' W ht H.1
  exact ⟨e', HE, ⟨HR, ProofShape.pi_inert_head_liftN H.2⟩, EE⟩

/-- One segment computing a constant lambda lowers its body at exactly the
body's original count. Annotation computation supplies the next actual domain
but contributes no primitive occurrences to the lower payload path. -/
theorem pi_inert_constant_lambda_count_segment
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T) (hΔ : proofEraseCtx Γ = Δ)
    (RA : ScopedComputeCount (PiInertStage D n) ca Δ (proofErase Γ A) rawA)
    (RB : ScopedComputeCount (PiInertStage D n) cb (proofErase Γ A :: Δ)
      ((proofErase Γ e).liftN 1) rawB) :
    ∃ A' e', env.IsDefEq univs Γ A A' (.sort u) ∧ env.IsDefEq univs Γ e e' T ∧
      proofErase Γ A' = rawA ∧ (proofErase Γ e').liftN 1 = rawB ∧
      ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') := by
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ hA hΔ rfl RA.forget
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EΓ : proofEraseCtx (A :: Γ) = _ := congrArg (List.cons (proofErase Γ A)) hΔ
  obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_count_descend
    (pi_inert_stage_rule_descent heq hs) hΓ hΓA Ctx.LiftN.one ht EΓ RB
  exact ⟨A', e', HA, HE, EA, EE, RE⟩

/-- Through a complete lambda path with changing annotations, an unused body
still descends with a count no larger than the original lambda computation. -/
theorem pi_inert_constant_lambda_count_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T) (hΔ : proofEraseCtx Γ = Δ)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) out) :
    ∃ A' e' k, k ≤ cost ∧ env.IsDefEq univs Γ A A' (.sort u) ∧ env.IsDefEq univs Γ e e' T ∧
      out = .lam (proofErase Γ A') ((proofErase Γ e').liftN 1) ∧
      ScopedComputeCount (PiInertStage D n) k (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') := by
  generalize E : ProofShape.lam (proofErase Γ A) ((proofErase Γ e).liftN 1) = source at R
  induction R generalizing Γ A e u T with
  | base H => exact (pi_inert_stage_no_lam (E ▸ H)).elim
  | beta H =>
    cases E
    obtain ⟨rawA, rawB, EO, RA, RB⟩ := H.lam_inv
    obtain ⟨A', e', HA, HE, EA, EB, RE⟩ := pi_inert_constant_lambda_count_segment heq hs
      hΓ hA ht hΔ (.beta RA) (.beta RB)
    exact ⟨A', e', 0, Nat.le_refl _, HA, HE, by simpa only [EA, EB] using EO, RE⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A', e', k₁, hk₁, HA₁, HE₁, EO₁, RE₁⟩ := ih₁ hΓ hA ht hΔ E
    obtain ⟨A'', e'', k₂, hk₂, HA₂, HE₂, EO₂, RE₂⟩ :=
      ih₂ hΓ HA₁.hasType.2 HE₁.hasType.2 hΔ EO₁.symm
    exact ⟨A'', e'', k₁+k₂, by omega, HA₁.trans HA₂, HE₁.trans HE₂, EO₂, RE₁.trans RE₂⟩
  | lam RA RB =>
    cases E
    obtain ⟨A', e', HA, HE, EA, EB, RE⟩ := pi_inert_constant_lambda_count_segment heq hs hΓ hA ht hΔ RA RB
    exact ⟨A', e', _, by omega, HA, HE, by rw [EA, EB], RE⟩
  | app | proj | forallE => cases E

/-- First head beta with an explicit accounting of the function path,
all argument paths and the final tail. Their total primitive count is bounded
by the original path, even when the first beta occurs beneath pending arguments. -/
theorem ProofShape.ScopedComputeCount.pi_inert_lambda_spine_or_beta
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps (.lam A b) args) out) :
    (∃ A' b' args' cf ca, cf+ca ≤ cost ∧ out = ProofShape.mkApps (.lam A' b') args' ∧
      ScopedComputeCount (PiInertStage D n) cf Δ (.lam A b) (.lam A' b') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args args') ∨
    (∃ A' b' x' xs' cf ca ct, cf+ca+ct ≤ cost ∧
      ScopedComputeCount (PiInertStage D n) cf Δ (.lam A b) (.lam A' b') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
      ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps (b'.inst x') xs') out) := by
  generalize E : ProofShape.mkApps (.lam A b) args = source at R
  induction R generalizing A b args with
  | base H =>
    rcases H.2 with HP | ⟨u, HS⟩
    · exact (lambda_spine_not_primitive A b args (E ▸ HP)).elim
    · have ES := E.trans HS
      cases args using List.snoc_induction with
      | nil => cases ES
      | snoc args a => rw [mkApps_snoc] at ES; cases ES
  | beta H =>
    cases E
    rcases beta_lambda_spine H with ⟨A', b', args', EO, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · exact .inl ⟨A', b', args', 0, 0, by omega, EO, .beta RF, .beta RX⟩
    · exact .inr ⟨A', b', x', xs', 0, 0, 0, by omega, .beta RF, .beta RX, .beta RT⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', args', cf, ca, hc, rfl, RF, RX⟩ |
      ⟨A', b', x', xs', cf, ca, ct, hc, RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', args'', cf', ca', hc', EO, RF', RX'⟩ |
        ⟨A'', b'', x'', xs'', cf', ca', ct', hc', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', args'', cf+cf', ca+ca', by omega, EO, RF.trans RF', RX.trans RX'⟩
      · exact .inr ⟨A'', b'', x'', xs'', cf+cf', ca+ca', ct', by omega,
          RF.trans RF', RX.trans RX', RT⟩
    · exact .inr ⟨A', b', x', xs', cf, ca, _, by omega, RF, RX, RT.trans R₂⟩
  | @app c₁ Δ f f' c₂ x x' RF RX ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := lambda_spine_app E
    rcases ihf rfl with ⟨A', b', args', cf, ca, hc, rfl, RF', RX'⟩ |
      ⟨A', b', x₀, xs', cf, ca, ct, hc, RF', RX', RT⟩
    · exact .inl ⟨A', b', args' ++ [x'], cf, ca+c₂, by omega,
        mkApps_snoc.symm, RF', RX'.append (.cons RX .nil)⟩
    · refine .inr ⟨A', b', x₀, xs' ++ [x'], cf, ca+c₂, ct, by omega,
        RF', RX'.append (.cons RX .nil), ?_⟩
      simpa only [mkApps_snoc, Nat.add_zero] using ScopedComputeCount.app RT (ScopedComputeCount.beta BetaRed.refl)
  | lam RA RB =>
    obtain ⟨rfl, rfl, rfl⟩ := lambda_spine_lam E
    exact .inl ⟨_, _, [], _, 0, by omega, rfl, .lam RA RB, .nil⟩
  | proj | forallE =>
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E

/-- Removing an identity wrapper at a function prefix never increases the
outer primitive count. The final output must have consumed the lambda spine. -/
theorem ProofShape.ScopedComputeCount.pi_inert_identity_spine_eliminate
    (hout : ∀ A' b' args', out ≠ ProofShape.mkApps (.lam A' b') args')
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.app (.lam A (.bvar 0)) e) args) out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ (ProofShape.mkApps e args) out := by
  change ScopedComputeCount (PiInertStage D n) cost Δ
    (ProofShape.mkApps (.lam A (.bvar 0)) (e :: args)) out at R
  rcases R.pi_inert_lambda_spine_or_beta with ⟨A', b', args', cf, ca, _, EO, _, _⟩ |
    ⟨A', b', x', xs', cf, ca, ct, hc, RF, RX, RT⟩
  · exact (hout A' b' args' EO).elim
  · obtain ⟨A'', EF, _⟩ := RF.forget.pi_inert_identity_lam
    cases EF
    cases RX with
    | cons RE RX =>
      refine ⟨_, by omega, (RE.mkApps RX).trans (n := ct) ?_⟩
      simpa only [ProofShape.inst, ProofShape.subst, ProofShape.Subst.liftN,
        ProofShape.Subst.one, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using RT

/-- Removing a constant wrapper at a function prefix likewise never increases
the count. The lowered body retains its count bound and the discarded first
argument contributes no remaining primitives. -/
theorem pi_inert_constant_spine_count_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (hout : ∀ A' b' args', out ≠ ProofShape.mkApps (.lam A' b') args')
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Γ)
      (ProofShape.mkApps (.app (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) x) args) out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k (proofEraseCtx Γ)
      (ProofShape.mkApps (proofErase Γ e) args) out := by
  change ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Γ)
    (ProofShape.mkApps (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) (x :: args)) out at R
  rcases R.pi_inert_lambda_spine_or_beta with ⟨A', b', args', cf, ca, _, EO, _, _⟩ |
    ⟨A', b', x', xs', cf, ca, ct, hc, RF, RX, RT⟩
  · exact (hout A' b' args' EO).elim
  · obtain ⟨A'', e', cb, hb, _, _, EF, RE⟩ :=
      pi_inert_constant_lambda_count_readout heq hs hΓ hA ht rfl RF
    cases EF
    cases RX with
    | cons _ RX =>
      refine ⟨_, by omega, (RE.mkApps RX).trans (n := ct) ?_⟩
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using RT

/-- A typed constant/identity expansion at a function prefix can be bypassed
with at most the tail's primitive count. Including the removed root makes this
a strict decrease; guard derivation sizes play no role in this measure. -/
theorem pi_inert_expansion_prefix_count_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps target pending) out)
    (HE : CarrierExposure out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ (ProofShape.mkApps source pending) out := by
  rcases H with H | H
  · obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
    cases H with
    | intro _ =>
      have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
        .sort (by trivial)
      have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
        if_neg (not_isProof_of_sort hΓ hA)
      exact pi_inert_constant_spine_count_eliminate heq hs hΓ hA ht HE.not_lambda_spine
        (by simpa only [EA, ProofShape.constantExpansion] using RT)
  · cases H with
    | intro _ => exact RT.pi_inert_identity_spine_eliminate HE.not_lambda_spine

end Lean4Lean.VEnv.Strengthening
