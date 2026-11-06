import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCompositionBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking

/-! # Retain carriers for terms and recover comparison for types

Ordinary Pi-inert comparison cannot cover all strong equalities: the empty-unit
boundary already refutes that predicate. Carrier evidence handles this case
without changing the primitive skeleton. At independently sort-typed endpoints,
it recovers ordinary comparison at the same stage, including all future typed
substitutions and core residuals. General carrier composition remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Carrier checking retains arbitrary independent ordinary-core reductions
of both endpoints. The actual assigned carrier is retained, not inferred from
an arbitrary intermediate raw comparison. -/
def PiInertCarrierInterpret (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop :=
  ∀ {a' b'}, Compute (ErasedLevelCore D) a a' → Compute (ErasedLevelCore D) b b' →
    ComputedJointCarrierGuard (PiInertStage D stage) Δ C a' b'

/-- A carrier interpretation together with every interpreted typed substitution
of its carrier and endpoints. This is evidence to construct, not a completeness
assumption for strong derivations or a type-conversion oracle. -/
structure PiInertCarrierEvidence (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop where
  base : PiInertCarrierInterpret D stage Δ C a b
  future : ∀ {Δ' τ}, ContextSubstitution Δ Δ' τ →
    PiInertCarrierInterpret D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ)

/-- A retained comparison is valid as a carrier guard at every supplied
carrier. Future substitutions preserve the same comparison evidence. -/
theorem PiInertEvidence.carrier
    (H : PiInertEvidence D stage (.compare true) Δ a b) : PiInertCarrierEvidence D stage Δ C a b := by
  refine ⟨fun RA RB => .carrierChecked (H.base RA RB), ?_⟩
  intro Δ' τ W a' b' RA RB
  exact .carrierChecked (H.future W RA RB)

/-- Future carrier evidence composes interpreted substitutions exactly. -/
theorem PiInertCarrierEvidence.substitute
    (H : PiInertCarrierEvidence D stage Δ C a b) (W : ContextSubstitution Δ Δ' τ) :
    PiInertCarrierEvidence D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.comp V)

/-- Carrier symmetry keeps the actual carrier and all future instances. -/
theorem PiInertCarrierEvidence.symm (H : PiInertCarrierEvidence D stage Δ C a b) :
    PiInertCarrierEvidence D stage Δ C b a := by
  refine ⟨fun RA RB => .carrierSymm (H.base RB RA), ?_⟩
  intro Δ' τ W a' b' RA RB
  exact .carrierSymm (H.future W RB RA)

/-- Empty-structure carrier checking accepts arbitrary endpoints and all their
future core residuals and substitutions, already at stage zero. This repairs
the unit-variable case rejected by ordinary Pi-inert comparison. -/
theorem pi_inert_unit_carrier_evidence
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0) :
    PiInertCarrierEvidence D stage Δ (.const family ls) a b := by
  refine ⟨fun _ _ => .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm), ?_⟩
  intro Δ' τ _ a' b' _ _
  exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- At independently sort-typed endpoints, carrier interpretation yields
ordinary common comparison at the unchanged Pi-inert stage. Core replay
preserves both the sort typings and the left endpoint's assigned carrier. -/
theorem PiInertCarrierInterpret.types_checked
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (haC : env.HasType univs Γ a C)
    (H : PiInertCarrierInterpret D stage (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertInterpret D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) := by
  intro left right RA RB
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ha rfl rfl (RA.scoped (fun R => .base R))
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hb rfl rfl (RB.scoped (fun R => .base R))
  have HC := H RA RB
  rw [← EA, ← EB] at HC ⊢
  exact proofErase_computed_carrier_types_checked
    (fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs stage
      hΓ hΓ' W ht (pi_inert_stage_embed R))
    hΓ HA.hasType.2 HB.hasType.2 (.inl (HA.toU.of_l henv hΓ haC).hasType.2) HC

/-- The carrier-to-type-comparison bridge retains future typed substitutions.
Consequently a carrier-based strong induction could still use the previously
proved whole-Pi domain extraction and converted-lambda eta rules unchanged. -/
theorem PiInertCarrierEvidence.types_checked
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (haC : env.HasType univs Γ a C)
    (H : PiInertCarrierEvidence D stage (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨PiInertCarrierInterpret.types_checked heq hs hΓ ha hb haC H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨w, hC⟩ := haC.isType henv hΓ
  have H' : PiInertCarrierInterpret D stage Δ' ((proofErase Γ C).subst τ)
      ((proofErase Γ a).subst τ) ((proofErase Γ b).subst τ) := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hC ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES]
  intro left right RA RB
  exact PiInertCarrierInterpret.types_checked heq hs hΓ₀
    (ha.subst henv.orderedStrong WS hΓ₀) (hb.subst henv.orderedStrong WS hΓ₀)
    (haC.subst henv.orderedStrong WS hΓ₀) H' RA RB

/-- At sort-typed endpoints the two hereditary predicates are equivalent,
with exactly the same stage, substitutions and full-core residual coverage.
Retaining a carrier therefore loses no previously constructed type evidence. -/
theorem pi_inert_carrier_types_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (haC : env.HasType univs Γ a C) :
    PiInertCarrierEvidence D stage (proofEraseCtx Γ) (proofErase Γ C)
        (proofErase Γ a) (proofErase Γ b) ↔
      PiInertEvidence D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) :=
  ⟨fun H => H.types_checked heq hs hΓ ha hb haC, fun H => H.carrier⟩

/-- In the actual typed unit-variable case, hereditary carrier evidence
exists at zero although hereditary comparison fails at every stage. The
separation is compatible with the proved equivalence for sort-typed endpoints. -/
theorem pi_inert_unit_carrier_separation
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    PiInertCarrierEvidence D 0 (proofEraseCtx Γ) (proofErase Γ (.const family ls))
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) ∧
      ∀ n mode, ¬ PiInertEvidence D n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  constructor
  · rw [show proofErase Γ (.const family ls) = .const family ls from
      if_neg (not_isProof_of_sort hΓ hS)]
    exact pi_inert_unit_carrier_evidence hi hp hx hf
  · intro n mode H
    have HC := H.base .refl .refl
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hiT),
      show proofErase Γ (.bvar j) = .bvar j from if_neg (not_proof_at_positive_type hΓ hS hjT)] at HC
    exact hne HC.pi_inert_bvar_injective

end Lean4Lean.VEnv.Strengthening
