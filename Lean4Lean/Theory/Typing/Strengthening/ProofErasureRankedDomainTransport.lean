import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDomainExposure

/-! # Finite-stage transport at actual smaller strong children

Computation stage and strong derivation rank have separate roles. A conversion
edge may increase the finite stage arbitrarily while remaining a strictly
smaller strong child. Both directions are retained without synthesizing a new
strong symmetry derivation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Missing carrier-transport component of a prospective simultaneous strong
induction. It permits arbitrary finite output stages and requires both
orientations at the original equality rank. No general coverage is asserted. -/
def FiniteCarrierTransport (D : Definitions) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∀ x y, (∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ A) x y) ↔
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ B) x y

/-- Missing computational-domain-transport component. The output need not use
the input stage. Bidirectionality is part of the hypothesis, rather than a
new recursive call on a higher-rank symmetrized strong equality. -/
def FiniteDomainTransport (D : Definitions) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∀ x y, (∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ A) x y) ↔
    ∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ B) x y

/-- Symmetry swaps the already retained directions and introduces no new
strong derivation, computation certificate or stage bound. -/
theorem FiniteDomainTransport.symm (H : FiniteDomainTransport D Γ A B) :
    FiniteDomainTransport D Γ B A := fun x y => (H x y).symm

/-- Transitivity composes finite-stage promises. The second transport consumes
the actual stage produced by the first, with no uniform stage-growth premise. -/
theorem FiniteDomainTransport.trans (H : FiniteDomainTransport D Γ A B)
    (K : FiniteDomainTransport D Γ B C) : FiniteDomainTransport D Γ A C :=
  fun x y => (H x y).trans (K x y)

/-- Actual ordinary-core joins prove both domain-transport directions. This
is stronger than a single directed interpreted computation prefix. -/
theorem finite_domain_transport_of_core_join
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (R : ComputeJoin (ErasedLevelCore D) (proofErase Γ A) (proofErase Γ B)) :
    FiniteDomainTransport D Γ A B := by
  intro x y
  exact exists_congr fun n => pi_inert_domain_exposure_core_join_iff hc
    ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩ ⟨Γ, B, _, hΓ, rfl, hB, rfl⟩ R

/-- A native type trace is interpreted using only its original lower-rank
edges. Existential finite stages may change at every edge; finiteness of the
trace suffices, and no numeric stage-growth function is needed. -/
theorem BoundedTypeTrace.finite_domain_pullback
    (H : BoundedTypeTrace env univs rank Γ A B)
    (edge : ∀ {j X Y u}, j < rank → StrongBounded env univs j Γ X Y (.sort u) →
      FiniteDomainTransport D Γ X Y)
    (HB : PiInertDomainExposure D stage (proofEraseCtx Γ) (proofErase Γ B) x y) :
    ∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ A) x y :=
  H.pullback (fun T => ∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ T) x y)
    (fun hj HE HY => (edge hj HE x y).mpr HY) ⟨stage, HB⟩

/-- On typed literal Pis, bidirectional finite domain transport is exactly
bidirectional finite carrier transport at their domains. This calibrates the
simultaneous induction: the Pi case genuinely needs the carrier component,
rather than solving or weakening that component by changing its vocabulary. -/
theorem finite_domain_transport_forall_iff
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A::Γ) B (.sort v))
    (hA' : env.HasType univs Γ A' (.sort u')) (hB' : env.HasType univs (A'::Γ) B' (.sort v')) :
    FiniteDomainTransport D Γ (.forallE A B) (.forallE A' B') ↔
      FiniteCarrierTransport D Γ A A' := by
  have ht := HasType.forallE hA hB
  have ht' := HasType.forallE hA' hB'
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have E' : proofErase Γ (.forallE A' B') = .forallE (proofErase Γ A') (proofErase (A'::Γ) B') :=
    if_neg (not_isProof_of_sort hΓ ht')
  have L (x y) : (∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) x y) ↔
      ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ A) x y := by
    rw [E]
    exact exists_congr fun n => pi_inert_domain_exposure_literal_iff hc ⟨Γ, _, _, hΓ, rfl, ht, E⟩
  have R (x y) : (∃ n, PiInertDomainExposure D n (proofEraseCtx Γ) (proofErase Γ (.forallE A' B')) x y) ↔
      ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ A') x y := by
    rw [E']
    exact exists_congr fun n => pi_inert_domain_exposure_literal_iff hc ⟨Γ, _, _, hΓ, rfl, ht', E'⟩
  exact ⟨fun H x y => (L x y).symm.trans ((H x y).trans (R x y)),
    fun H x y => (L x y).trans ((H x y).trans (R x y).symm)⟩

/-- The function-type congruence case of domain transport uses exactly the
original domain child's carrier-transport hypothesis. Both codomain contexts
already carried by the strong rule supply typing of the literal outputs.
No domain injectivity or reconstructed equality is used. -/
theorem strong_forall_domain_transport
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : StrongBounded env univs rank Γ A A' (.sort u))
    (hB : StrongBounded env univs rank (A::Γ) B B' (.sort v))
    (hB' : StrongBounded env univs rank (A'::Γ) B B' (.sort v))
    (domain : FiniteCarrierTransport D Γ A A') :
    FiniteDomainTransport D Γ (.forallE A B) (.forallE A' B') :=
  (finite_domain_transport_forall_iff hc hΓ hA.strong.defeq.hasType.1 hB.strong.defeq.hasType.1
    hA.strong.defeq.hasType.2 hB'.strong.defeq.hasType.2).mpr domain

/-- The forallEDF parent invokes the simultaneous carrier hypothesis at rank
k strictly below k+1. Even the reverse direction uses that same child, rather
than its rank-(k+1) strong symmetry reconstruction. This discharges this one
constructor once the lower-rank carrier component is available. -/
theorem strong_forall_domain_transport_of_lower
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : StrongBounded env univs k Γ A A' (.sort u))
    (hB : StrongBounded env univs k (A::Γ) B B' (.sort v))
    (hB' : StrongBounded env univs k (A'::Γ) B B' (.sort v))
    (lower : ∀ {j X Y w}, j < k+1 → StrongBounded env univs j Γ X Y (.sort w) →
      FiniteCarrierTransport D Γ X Y) :
    FiniteDomainTransport D Γ (.forallE A B) (.forallE A' B') :=
  strong_forall_domain_transport hc hΓ hA hB hB' (lower (Nat.lt_succ_self k) hA)

/-- An arbitrary recovered type can compute to the witnessed Pi. The output
core tail transfers the domain guard to the exact Pi reached by recovery.
Neither the recovered type nor the function head must be literal syntax. -/
theorem PiInertDomainExposure.recovered_application
    (H : PiInertDomainExposure D n Δ T x y)
    (R : ScopedTypeRecovery (PiInertStage D n) Δ f T)
    (HF : ComputedJointCompare (PiInertStage D n) Δ false f g) :
    ComputedJointCompare (PiInertStage D n) Δ mode (.app f x) (.app g y) := by
  obtain ⟨A, B, HC, HA⟩ := H
  obtain ⟨shared, RS, RT⟩ := HC.base.2 .refl
  obtain ⟨A', B', rfl, RA, RB⟩ := RT.pi_parts (fun H => erased_level_core_no_pi H)
  exact .appCarrier (R.convert RS) HF (HA.base RA .refl .refl)

/-- The neutral appDF case consumes its actual argument-equality child and
its actual function-equality child. Lower domain-transport hypotheses may
choose larger finite stages at each native trace edge. The result is a raw
application comparison; arbitrary substituted function heads and hereditary
application histories remain separate unproved cases. -/
theorem strong_neutral_app_of_lower
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : StrongBounded env univs k Γ A A (.sort u))
    (hB : StrongBounded env univs k (A::Γ) B B (.sort v))
    (hF : StrongBounded env univs k Γ (.bvar i) (.bvar i) (.forallE A B))
    (hX : StrongBounded env univs k Γ x y A)
    (hl : Lookup Γ i T)
    (HX : proofErase Γ (.app (.bvar i) x) = .app (.bvar i) (proofErase Γ x))
    (HY : proofErase Γ (.app (.bvar i) y) = .app (.bvar i) (proofErase Γ y))
    (arguments : ∀ {j a b C}, j < k+1 → StrongBounded env univs j Γ a b C →
      ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C)
        (proofErase Γ a) (proofErase Γ b))
    (edges : ∀ {j X Y l}, j < k+1 → StrongBounded env univs j Γ X Y (.sort l) →
      FiniteDomainTransport D Γ X Y) :
    ∃ n, ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true
      (proofErase Γ (.app (.bvar i) x)) (proofErase Γ (.app (.bvar i) y)) := by
  obtain ⟨stage, HA⟩ := arguments (Nat.lt_succ_self k) hX
  have ht := HasType.forallE hA.strong.defeq hB.strong.defeq
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HP : PiInertDomainExposure D stage (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ x) (proofErase Γ y) := by
    rw [E]
    exact .literal hc ⟨Γ, _, _, hΓ, rfl, ht, E⟩ HA
  obtain ⟨n, HN⟩ := (hF.variable_native_trace hl).finite_domain_pullback
    (fun hj HE => edges (Nat.lt_trans hj (Nat.lt_succ_self k)) HE) HP
  have HO : contextOracle (proofEraseCtx Γ) i = proofErase Γ T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl]
  refine ⟨n, ?_⟩
  rw [HX, HY]
  apply HN.recovered_application ?_ (.leaf .refl)
  rw [← HO]
  exact .bvar


/-- Proposition-valued neutral appDF needs no supplied erasure-shape facts.
The actual function and argument children establish nonproof erasure, while
the lower-rank semantic hypotheses supply the argument and native-domain
certificates. This is the original neutral predicate application case with
arbitrary assigned and native domains, not a syntactic-domain fragment. -/
theorem strong_neutral_predicate_app_of_lower
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : StrongBounded env univs k Γ A A (.sort u))
    (hB : StrongBounded env univs k (A::Γ) (.sort .zero) (.sort .zero) (.sort v))
    (hF : StrongBounded env univs k Γ (.bvar i) (.bvar i) (.forallE A (.sort .zero)))
    (hX : StrongBounded env univs k Γ x y A)
    (hl : Lookup Γ i T)
    (arguments : ∀ {j a b C}, j < k+1 → StrongBounded env univs j Γ a b C →
      ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C)
        (proofErase Γ a) (proofErase Γ b))
    (edges : ∀ {j X Y l}, j < k+1 → StrongBounded env univs j Γ X Y (.sort l) →
      FiniteDomainTransport D Γ X Y) :
    ∃ n, ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true
      (proofErase Γ (.app (.bvar i) x)) (proofErase Γ (.app (.bvar i) y)) := by
  have hf := hF.strong.defeq.hasType.1
  have hx := hX.strong.defeq.hasType.1
  have hy := hX.strong.defeq.hasType.2
  have HF : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_function_to_sort hΓ hf)
  have hfx : env.HasType univs Γ (.app (.bvar i) x) (.sort .zero) := by
    simpa only [VExpr.inst] using hf.app hx
  have hfy : env.HasType univs Γ (.app (.bvar i) y) (.sort .zero) := by
    simpa only [VExpr.inst] using hf.app hy
  apply strong_neutral_app_of_lower hc hΓ hA hB hF hX hl ?_ ?_ arguments edges
  · rw [show proofErase Γ (.app (.bvar i) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hfx), HF]
  · rw [show proofErase Γ (.app (.bvar i) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hfy), HF]

end Lean4Lean.VEnv.Strengthening
