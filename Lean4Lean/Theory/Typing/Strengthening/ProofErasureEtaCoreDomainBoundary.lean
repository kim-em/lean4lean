import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaCoreResiduals
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilySubstitutionBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover

/-! # Exact strength of unrestricted eta-domain certificate coverage

Full-core histories do not restrict the semantic conversion hidden in an
assigned function type. Even a zero-step constant-body lambda exposes any
same-sort conversion as an eta domain mark. Finite inferred coverage of all
such marks is equivalent to finite inferred coverage of all same-sort equations,
and would imply the complete proposition front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Missing pointwise finite inferred coverage of all exposed eta-domain marks.
Every mark may choose its own finite stage; functions are required to be actual
non-proofs. The theorem below shows that this is not a smaller front obligation. -/
def FiniteEtaCoreDomainReadout (D : Definitions) : Prop :=
  ∀ {Γ A u f B C E}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ f (.forallE A B) → ¬ IsProof Γ f →
    EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E →
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) false C E

/-- Missing finite inferred coverage of arbitrary actual same-sort equations.
Each individual equation may choose any finite stage. -/
def FiniteInferredSortReadout (D : Definitions) : Prop :=
  ∀ {Γ P Q u}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ P (.sort u) →
    env.HasType univs Γ Q (.sort u) → env.IsDefEq univs Γ P Q (.sort u) →
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) false (proofErase Γ P) (proofErase Γ Q)

/-- A proposed restriction to sources with an existing stage-zero native Pi
and a certified input sort. Agreement between its native and assigned domains
is deliberately not assumed. This restriction still contains the full front. -/
def FiniteNativeEtaCoreDomainReadout (D : Definitions) : Prop :=
  ∀ {Γ A u f B X Y C E}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ f (.forallE A B) → ¬ IsProof Γ f →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y) →
    DomainSort (proofEraseCtx Γ) X u →
    EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E →
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) false C E

/-- A stronger proposed restriction: the starting function natively recovers
its exact assigned Pi at stage zero. An identity wrapper supplies this evidence
for any typed non-proof function, so it still does not make coverage smaller. -/
def FiniteAssignedEtaCoreDomainReadout (D : Definitions) : Prop :=
  ∀ {Γ A u f B C E}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ f (.forallE A B) → ¬ IsProof Γ f →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B)) →
    EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E →
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) false C E

/-- Prefixing the function's history preserves either orientation of every
domain mark; the written annotation and compared domain pair stay unchanged. -/
theorem ProofShape.EtaCoreDomains.function_prefix (H : EtaCoreDomains D A f C E)
    (R : Compute (ErasedLevelCore D) g f) : EtaCoreDomains D A g C E := by
  rcases H with ⟨RA, b, RF⟩ | ⟨RA, b, RF⟩
  · exact .inl ⟨RA, b, R.trans RF⟩
  · exact .inr ⟨RA, b, R.trans RF⟩

/-- Exact native recovery of the assigned source type does not restrict the
coverage problem. A single identity beta step removes that certificate while
retaining every domain mark of the arbitrary typed argument. -/
theorem FiniteAssignedEtaCoreDomainReadout.domains
    (H : FiniteAssignedEtaCoreDomainReadout D) : FiniteEtaCoreDomainReadout D := by
  intro Γ A u f B C E hΓ hA hf hn HG
  obtain ⟨hy, HE, RB, RN⟩ := proofErase_identity_recovery_cover
    (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ hf
  have hny := mt (isProof_congr hΓ HE).1 hn
  exact H hΓ hA hy hny (RN hny) (HG.function_prefix (.beta RB))

/-- Two actual domains realize an exposed mark at its original input sort.
Their semantic equality follows from computation and the assigned Pi typing;
this supplies no inferred comparison certificate. -/
theorem proofErase_eta_core_domain_realize (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E) :
    ∃ C₀ E₀, env.HasType univs Γ C₀ (.sort u) ∧ env.HasType univs Γ E₀ (.sort u) ∧
      env.IsDefEq univs Γ C₀ E₀ (.sort u) ∧ proofErase Γ C₀ = C ∧ proofErase Γ E₀ = E := by
  have expose {X Y body}
      (RA : Compute (ErasedLevelCore D) (proofErase Γ A) X)
      (RF : Compute (ErasedLevelCore D) (proofErase Γ f) (.lam Y body)) :
      ∃ X₀ Y₀, env.HasType univs Γ X₀ (.sort u) ∧ env.HasType univs Γ Y₀ (.sort u) ∧
        env.IsDefEq univs Γ X₀ Y₀ (.sort u) ∧ proofErase Γ X₀ = X ∧ proofErase Γ Y₀ = Y := by
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hA rfl rfl (RA.scoped (fun H => .base H))
    obtain ⟨g, HG, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hf rfl rfl (RF.scoped (fun H => .base H))
    have hg := HG.hasType.2
    obtain ⟨C', b, rfl, _, EC, _⟩ := erase_lam_inv EG
    obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
    obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
    have HAC := HCA.toU.symm.of_l henv hΓ hA
    exact ⟨A', C', HA.hasType.2, HAC.hasType.2, HA.symm.trans HAC, EA, EC⟩
  rcases H with ⟨RA, body, RF⟩ | ⟨RA, body, RF⟩
  · exact expose RA RF
  · obtain ⟨E₀, C₀, hE, hC, HE, EE, EC⟩ := expose RA RF
    exact ⟨C₀, E₀, hC, hE, HE.symm, EC, EE⟩

/-- No computation is needed to expose an arbitrary same-sort conversion as
an eta-domain mark. A constant-body lambda uses the converted assigned domain. -/
theorem FiniteEtaCoreDomainReadout.sort_readout (H : FiniteEtaCoreDomainReadout D) :
    FiniteInferredSortReadout D := by
  intro Γ P Q u hΓ hP hQ HPQ
  have hf : env.HasType univs Γ (domainProbe Q) (.forallE P (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF HPQ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hQ)
  apply H hΓ hP hf (not_isProof_function_to_sort hΓ hf)
  apply Or.inl
  refine ⟨.refl, .sort .zero, ?_⟩
  rw [proofErase_domainProbe hΓ hQ]
  exact .refl

/-- The zero-step probe already has a stage-zero native Pi and a typed
native domain. Merely adding source native recovery does not remove the
arbitrary converted assignment that the domain readout must compare. -/
theorem FiniteNativeEtaCoreDomainReadout.sort_readout (H : FiniteNativeEtaCoreDomainReadout D) :
    FiniteInferredSortReadout D := by
  intro Γ P Q u hΓ hP hQ HPQ
  have hf : env.HasType univs Γ (domainProbe Q) (.forallE P (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF HPQ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hQ)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ (domainProbe Q))
      (.forallE (proofErase Γ Q) (.sort (.succ .zero))) := by
    rw [proofErase_domainProbe hΓ hQ]
    exact .lam (.sort (by trivial))
  apply H hΓ hP hf (not_isProof_function_to_sort hΓ hf) RN (DomainSort.of_typed hΓ hQ)
  refine .inl ⟨.refl, .sort .zero, ?_⟩
  rw [proofErase_domainProbe hΓ hQ]
  exact .refl

/-- Conversely, unrestricted same-sort certificates cover every recorded
eta-domain mark by realization. The computation histories add no restriction
to the global coverage obligation. -/
theorem FiniteInferredSortReadout.eta_domains (hs : D.Sound env univs)
    (H : FiniteInferredSortReadout D) : FiniteEtaCoreDomainReadout D := by
  intro Γ A u f B C E hΓ hA hf _ HG
  obtain ⟨C₀, E₀, hC, hE, HCE, EC, EE⟩ := proofErase_eta_core_domain_realize hs hΓ hA hf HG
  obtain ⟨stage, HC⟩ := H hΓ hC hE HCE
  exact ⟨stage, by simpa only [EC, EE] using HC⟩

/-- The full-history domain obligation is exactly unrestricted finite inferred
sort coverage, not a syntactically restricted domain problem. -/
theorem finite_eta_core_domains_iff_sort_readout (hs : D.Sound env univs) :
    FiniteEtaCoreDomainReadout D ↔ FiniteInferredSortReadout D :=
  ⟨fun H => H.sort_readout, fun H => H.eta_domains hs⟩

/-- Stage-zero source recovery and a domain-sort witness do not weaken the
unrestricted coverage requirement. A certificate relating the assigned and
native domains would be extra information, not a consequence of these inputs. -/
theorem finite_native_eta_core_domains_iff_sort_readout (hs : D.Sound env univs) :
    FiniteNativeEtaCoreDomainReadout D ↔ FiniteInferredSortReadout D := by
  refine ⟨fun H => H.sort_readout, ?_⟩
  intro H Γ A u f B X Y C E hΓ hA hf hn _ _ HG
  exact H.eta_domains hs hΓ hA hf hn HG

/-- Even exact assigned-Pi recovery at the initial source leaves global
eta-domain readout equivalent to unrestricted inferred same-sort coverage. -/
theorem finite_assigned_eta_core_domains_iff_sort_readout (hs : D.Sound env univs) :
    FiniteAssignedEtaCoreDomainReadout D ↔ FiniteInferredSortReadout D := by
  refine ⟨fun H => FiniteEtaCoreDomainReadout.sort_readout H.domains, ?_⟩
  intro H Γ A u f B C E hΓ hA hf hn _ HG
  exact H.eta_domains hs hΓ hA hf hn HG

/-- Inferred same-sort certificates above one unused binder descend directly
to the complete proposition front. Neither core nor expansion confluence is
needed, and each certificate may choose its own stage. -/
theorem FiniteInferredSortReadout.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FiniteInferredSortReadout D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨stage, HC⟩ := H hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  rw [proofErase_liftN hΓ hΓ' Ctx.LiftN.one hP,
    proofErase_liftN hΓ hΓ' Ctx.LiftN.one hR] at HC
  exact (proofErase_computed_joint_compare_descend
    (erased_static_structure_eta_expansion_stage_descent heq hs stage)
    hΓ hΓ' Ctx.LiftN.one rfl hP hR HC).2 rfl
      (not_isProof_of_sort hΓ hP) (not_isProof_of_sort hΓ hR)

/-- Finite readout of all eta-domain histories already implies the original
front. This does not refute readout or strengthening; it rules out claiming
this obligation is a strictly smaller sufficient final deliverable. -/
theorem FiniteEtaCoreDomainReadout.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FiniteEtaCoreDomainReadout D) : PropositionFront :=
  FiniteInferredSortReadout.implies_propositionFront heq hs H.sort_readout

/-- The native-source restriction still implies the complete canonical-Eq
front, already on zero-step lambda histories and with arbitrary output stages. -/
theorem FiniteNativeEtaCoreDomainReadout.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FiniteNativeEtaCoreDomainReadout D) : PropositionFront :=
  FiniteInferredSortReadout.implies_propositionFront heq hs H.sort_readout

/-- An exact assigned native Pi at stage zero still contains the full front.
The additional function history needed by the reduction is one identity beta. -/
theorem FiniteAssignedEtaCoreDomainReadout.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FiniteAssignedEtaCoreDomainReadout D) : PropositionFront :=
  FiniteEtaCoreDomainReadout.implies_propositionFront heq hs H.domains

omit [Params] in
/-- The barrier applies to the actual environment core with its total stored
definitions, not just an abstract choice of primitive computation. -/
theorem EnvironmentCore.native_eta_domain_readout_implies_propositionFront
    {E : VEnv} (hE : E.WF) (U : Nat) :
    letI := hE.params U
    E.HasCanonicalEq → FiniteNativeEtaCoreDomainReadout definitions → PropositionFront := by
  letI := hE.params U
  intro heq H
  exact FiniteNativeEtaCoreDomainReadout.implies_propositionFront heq sound H

omit [Params] in
/-- The exact assigned-source certificate restriction also contains the whole
front for the actual total environment core. -/
theorem EnvironmentCore.assigned_eta_domain_readout_implies_propositionFront
    {E : VEnv} (hE : E.WF) (U : Nat) :
    letI := hE.params U
    E.HasCanonicalEq → FiniteAssignedEtaCoreDomainReadout definitions → PropositionFront := by
  letI := hE.params U
  intro heq H
  exact FiniteAssignedEtaCoreDomainReadout.implies_propositionFront heq sound H

end Lean4Lean.VEnv.Strengthening
