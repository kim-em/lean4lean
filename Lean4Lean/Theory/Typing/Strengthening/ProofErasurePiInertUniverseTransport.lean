import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierTransport

/-! # Carrier transport at arbitrary universe aliases

An actual universe alias cannot computationally expose a structural carrier.
Consequently its carrier guards contain ordinary endpoint comparisons even
for untyped raw endpoints. This constructs the full transport certificate
without an exposure path or a certificate for the actual type equality.
The original strong conversion-to-universe case then needs no additional
semantic type-child premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- An actual type equal to a universe, recorded at its raw erasure. No
computation to a literal sort is asserted. The witness is ordinary typing
and equality in an actual context realizing the raw context. -/
def ProofShape.UniverseAlias (Δ : List ProofShape) (T : ProofShape) : Prop :=
  ∃ Γ A u v, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.IsDefEq univs Γ A (.sort v) (.sort u) ∧ proofErase Γ A = T

/-- Actual universe equality supplies the alias witness directly. -/
theorem ProofShape.UniverseAlias.of_typed
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ T (.sort v) (.sort u)) :
    UniverseAlias (proofEraseCtx Γ) (proofErase Γ T) := ⟨Γ, T, u, v, hΓ, rfl, H, rfl⟩

/-- Ordinary forward substitution preserves the universe alias witness.
This moves actual equality, not a guarded computation certificate. -/
theorem ProofShape.UniverseAlias.substitute (H : UniverseAlias Δ T)
    (W : ContextSubstitution Δ Λ σ) : UniverseAlias Λ (T.subst σ) := by
  obtain ⟨Γ, A, u, v, hΓ, EΓ, HE, EA⟩ := H
  obtain ⟨Γ', τ, hΓ', EΓ', WT, ES⟩ := W hΓ EΓ
  refine ⟨Γ', A.subst τ, u, v, hΓ', EΓ', ?_, ?_⟩
  · simpa only [VExpr.subst] using HE.subst henv.orderedStrong WT hΓ'
  · rw [proofErase_subst_with hΓ' WT HE.hasType.1 ES, EA]

/-- No finite Pi-inert path from an actual universe alias exposes a function
or structure carrier. Sound realization followed by rigid head inversion
proves this without source or target typings for any compared operands. -/
theorem ProofShape.UniverseAlias.no_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : UniverseAlias Δ T) (R : ScopedCompute (PiInertStage D n) Δ T out) :
    ¬ CarrierExposure out := by
  obtain ⟨Γ, A, u, v, hΓ, EΓ, HE, EA⟩ := H
  obtain ⟨B, HB, EB⟩ := proofErase_scoped_compute_realize
    (fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed R)) hΓ HE.hasType.1 EΓ EA R
  have HU := (HE.symm.trans HB).toU
  intro HX
  cases HX with
  | function =>
    obtain ⟨C, E, rfl, _, _, _⟩ := erase_forallE_inv EB
    exact HU.sort_forallE_inv henv hΓ
  | record hi hx hp =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EB
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HU.typeChain henv hΓ HE.hasType.2)

/-- At a universe alias, every carrier guard is already an ordinary common
comparison of its raw endpoints. No endpoint typing is needed: the selected
carrier alone excludes all structural checking alternatives. -/
theorem ProofShape.UniverseAlias.carrier_checked
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : UniverseAlias Δ T)
    (HC : ComputedJointCarrierGuard (PiInertStage D n) Δ T a b) :
    ComputedJointCompare (PiInertStage D n) Δ true a b := by
  rcases HC.checked_or_exposed with HC | ⟨out, R, HX, _⟩
  · exact HC
  · exact (H.no_carrier_exposure heq hs R HX).elim

/-- A universe-alias history reindexes to any carrier at the same stage,
including all core-world futures and independent endpoint residuals. Unlike
the older sorted-endpoint lemma, this works for arbitrary raw endpoints. -/
theorem PiInertWorldHistory.universe_alias_reindex
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : UniverseAlias Δ T) (H : PiInertWorldHistory D n Δ T a b) :
    PiInertWorldHistory D n Δ U a b := by
  refine ⟨fun _ RA RB => .carrierChecked (HT.carrier_checked heq hs (H.base .refl RA RB)), ?_⟩
  intro Λ σ W U' a' b' _ RA RB
  exact .carrierChecked ((HT.substitute W.typed).carrier_checked heq hs
    (H.future W .refl RA RB))

/-- Any two actual universe aliases construct the full carrier-transport
certificate. Their universes need not agree: the certificate transports
histories, and does not assert ordinary equality of the selected types.
Actual operand assignments remain separate premises of conversion consumers. -/
theorem PiInertCarrierTransport.universe_aliases
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : UniverseAlias Δ T) (HU : UniverseAlias Δ U) :
    PiInertCarrierTransport D Δ T U := by
  intro Λ σ W a b
  exact ⟨fun ⟨n, H⟩ => ⟨n, H.universe_alias_reindex heq hs (HT.substitute W)⟩,
    fun ⟨n, H⟩ => ⟨n, H.universe_alias_reindex heq hs (HU.substitute W)⟩⟩

/-- Explicit guarded calls are impossible at a universe alias. A retained
call exposure meets a core reduct of a literal Pi, which is still a literal
Pi, contradicting universe head separation. Thus every realizable finite
tree here consists of ordinary leaves and their intersections. -/
theorem PiInertGuardedTreeValue.ordinary_of_universe_alias
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : UniverseAlias Δ T) (H : PiInertGuardedTreeValue p ρ D Δ a b T) :
    p.Ordinary := by
  induction p with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1, ihq H.2⟩
  | call A B p q =>
    obtain ⟨n, R⟩ := H.2.1
    obtain ⟨out, RT, RP⟩ := R.base.2 .refl
    obtain ⟨A', B', rfl, _, _⟩ := RP.pi_parts (fun R => erased_level_core_no_pi R)
    exact HT.no_carrier_exposure heq hs RT .function

/-- Assigned ground evidence for sorted endpoints constructs any ordinary
tree, including finite intersections and arbitrary ordinary arrow demands
inside its leaves. These arrows have no actual application tests. -/
theorem PiInertAssignedBase.sorted_tree
    (H : PiInertAssignedBase D Δ a b T) (S : DomainSort Δ a u) (HP : p.Ordinary) :
    PiInertGuardedTreeValue p ρ D Δ a b T := by
  induction p with
  | plain => exact ⟨H.left, H.right, H.ground.sorted_demand S⟩
  | both p q ihp ihq => exact ⟨ihp HP.1, ihq HP.2⟩
  | call => exact HP.elim

/-- Every paired interpreter retains its assigned ground interpreter without
changing the original endpoints, selected types or variable requirements. -/
theorem PiInertGuardedPairInterpretation.ground
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U p q) :
    PiInertGuardedPairInterpretation D Δ uses a b T U (.plain .ground) (.plain .ground) := by
  refine ⟨H.left, H.right, ?_⟩
  intro Λ σ τ WL WR images
  have K := H.run WL WR images
  exact ⟨⟨K.forward.base.left, K.forward.base.right, K.forward.base.ground⟩,
    ⟨K.backward.base.left, K.backward.base.right, K.backward.base.ground⟩⟩

/-- Sorted original endpoints construct every ordinary result tree under the
same paired environments. This does not change their selected assignments. -/
theorem PiInertGuardedPairInterpretation.sorted_trees
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U p q)
    (SA : DomainSort Δ a u) (SB : DomainSort Δ b v) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D Δ uses a b T U r s := by
  refine ⟨H.left, H.right, ?_⟩
  intro Λ σ τ WL WR images
  have K := H.run WL WR images
  exact ⟨K.forward.base.sorted_tree (ContextSubstitution.sort WL SA) HR,
    K.backward.base.sorted_tree (ContextSubstitution.sort WR SB) HS⟩

/-- An original strong type child whose right endpoint is a universe
constructs its carrier-transport certificate. No interpreted type comparison,
directed exposure or separate history-transport hypothesis remains here. -/
theorem StrongBounded.universe_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs k Γ T (.sort v) (.sort u)) :
    PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ (.sort v)) := by
  have HE := H.strong.defeq
  intro Λ σ W a b
  exact PiInertCarrierTransport.universe_aliases heq hs
    (.of_typed hΓ HE) (.of_typed hΓ HE.hasType.2) W a b

/-- A strong type child also constructs transport when the target is any
actual universe alias. Its target equality is used only as ordinary typing
evidence; no guarded path exposing that alias is required. -/
theorem StrongBounded.universe_alias_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs k Γ A B (.sort u))
    (HB : env.IsDefEq univs Γ B (.sort v) (.sort w)) :
    PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B) := by
  have HE := H.strong.defeq
  have HB' := HB.toU.of_l henv hΓ HE.hasType.2
  intro Λ σ W a b
  exact PiInertCarrierTransport.universe_aliases heq hs
    (.of_typed hΓ (HE.trans HB')) (.of_typed hΓ HB) W a b

/-- Ground interpretation closes the original strong conversion-to-universe
case from its term interpreter and original children alone. The type child's
transport is constructed by universe head separation, rather than supplied
as an extra semantic premise. General non-universe targets remain open. -/
theorem StrongBounded.paired_ground_convert_to_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A (.sort v) (.sort u))
    (termChild : StrongBounded env univs k Γ f g A)
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A)
      (.plain .ground) (.plain .ground)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.sort v)) (proofErase Γ (.sort v))
      (.plain .ground) (.plain .ground) :=
  StrongBounded.paired_ground_convert heq hs hΓ typeChild termChild
    (typeChild.universe_transport heq hs hΓ) H

/-- The original strong conversion-to-universe case constructs every
ordinary target tree from any supplied source interpreter. No semantic
transport premise is added to the original type child. The proved exclusion
of call nodes explains why this covers all realizable target tree shapes. -/
theorem StrongBounded.paired_convert_to_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A (.sort v) (.sort u))
    (termChild : StrongBounded env univs k Γ f g A)
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A) p q)
    (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.sort v)) (proofErase Γ (.sort v)) r s := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  have converted := StrongBounded.paired_ground_convert_to_universe heq hs hΓ typeChild termChild H.ground
  exact converted.sorted_trees (.of_typed hΓ (HE.defeq HF.hasType.1))
    (.of_typed hΓ (HE.defeq HF.hasType.2)) HR HS

/-- Conversion into a nonliteral universe alias also constructs all ordinary
target trees. The original strong children supply the new assignments and
the actual target equality supplies sorted endpoint witnesses. No interpreted
type comparison, exposure path or transport hypothesis is assumed. -/
theorem StrongBounded.paired_convert_universe_alias
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort u))
    (termChild : StrongBounded env univs k Γ f g A)
    (HB : env.IsDefEq univs Γ B (.sort v) (.sort w))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A) p q)
    (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) (proofErase Γ B) r s := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  have converted := StrongBounded.paired_ground_convert heq hs hΓ typeChild termChild
    (typeChild.universe_alias_transport heq hs hΓ HB) H.ground
  exact converted.sorted_trees (.of_typed hΓ (HB.defeq (HE.defeq HF.hasType.1)))
    (.of_typed hΓ (HB.defeq (HE.defeq HF.hasType.2))) HR HS

omit [Params] in
/-- Full environment cores support universe-alias transport from actual
equality alone. This does not require the alias to expose a literal universe
by ordinary or guarded computation. -/
theorem EnvironmentCore.universe_alias_transport
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ T u v}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.IsDefEq U Γ T (.sort v) (.sort u) →
      PiInertCarrierTransport definitions (proofEraseCtx Γ)
        (proofErase Γ T) (proofErase Γ (.sort v)) := by
  letI := henv.params U
  intro Γ T u v heq hΓ H Λ σ W a b
  exact PiInertCarrierTransport.universe_aliases heq sound
    (.of_typed hΓ H) (.of_typed hΓ H.hasType.2) W a b

end Lean4Lean.VEnv.Strengthening
