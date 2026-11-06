import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationPiDomains
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiJoinDomains
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiDomainComparison

/-! # Domain readout at core-exposed Pi endpoints

The induction interface allows comparison endpoints to expose typed Pis only
after core computation. This handles recursive computation prefixes without
assuming the intermediate outputs are literal Pis. The general certificate
coverage theorem, including prior guards and weakening, is not asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The domain-extraction induction invariant. Actual Pi components are
supplied at the observed residuals, not at the certificate's original endpoints.
Coverage for every CoreFamilyCast comparison remains to be proved. -/
def PiCoreDomainReadout (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∀ {Γ A B C E u v w z}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ A (.sort u) → env.HasType univs (A :: Γ) B (.sort v) →
    env.HasType univs Γ C (.sort w) → env.HasType univs (C :: Γ) E (.sort z) →
    proofEraseCtx Γ = Δ →
    Compute (ErasedLevelCore D) a (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) →
    Compute (ErasedLevelCore D) b (.forallE (proofErase Γ C) (proofErase (C :: Γ) E)) →
    ComputedJointCompare (ErasedStaticStructureEtaExpansionUnion D) Δ true (proofErase Γ A) (proofErase Γ C)

/-- Symmetry reverses the two observed Pi histories and their domain check. -/
theorem PiCoreDomainReadout.symm (H : PiCoreDomainReadout D Δ a b) : PiCoreDomainReadout D Δ b a := by
  intro Γ A B C E u v w z hΓ hA hB hC hE EΓ RA RB
  exact (H hΓ hC hE hA hB EΓ RB RA).symm

/-- Additional ordinary-core computation is absorbed into the observation
histories. No stage or comparison-transport premise is required. -/
theorem PiCoreDomainReadout.reducts (H : PiCoreDomainReadout D Δ a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiCoreDomainReadout D Δ a' b' := by
  intro Γ A B C E u v w z hΓ hA hB hC hE EΓ RL RR
  exact H hΓ hA hB hC hE EΓ (RA.trans RL) (RB.trans RR)

/-- Typed core-exposed Pi readout is preserved by two certified computation
prefixes. Readout of their wrapped outputs supplies the smaller comparison
child with core-exposed Pis, retaining paths from the original domains. -/
theorem PiCoreDomainReadout.prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HA : CoreFamilyCast D stage .compute Δ a a') (HB : CoreFamilyCast D stage .compute Δ b b')
    (H : PiCoreDomainReadout D Δ a' b') : PiCoreDomainReadout D Δ a b := by
  intro Γ A B C E u v w z hΓ hA hB hC hE EΓ RA RB
  obtain ⟨left, RL, CL⟩ := HA.commute heq hs hl hcon hc hreg hoff hD RA
  obtain ⟨right, RR, CR⟩ := HB.commute heq hs hl hcon hc hreg hoff hD RB
  obtain ⟨X, Y, ⟨A₁, B₁, HA₁, hB₁, EA₁, EB₁, RDA, _⟩, RβL⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB
      (EΓ ▸ RL.mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩))
  obtain ⟨Z, W, ⟨C₁, E₁, HC₁, hE₁, EC₁, EE₁, RDC, _⟩, RβR⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hC hE
      (EΓ ▸ RR.mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩))
  have HL : Compute (ErasedLevelCore D) a'
      (.forallE (proofErase Γ A₁) (proofErase (A₁ :: Γ) B₁)) := by
    simpa only [EA₁, EB₁] using CL.trans (.beta RβL)
  have HR : Compute (ErasedLevelCore D) b'
      (.forallE (proofErase Γ C₁) (proofErase (C₁ :: Γ) E₁)) := by
    simpa only [EC₁, EE₁] using CR.trans (.beta RβR)
  have HD := H hΓ HA₁.hasType.2 hB₁ HC₁.hasType.2 hE₁ EΓ HL HR
  rw [EA₁, EC₁] at HD
  exact .compute (EΓ ▸ RDA) (EΓ ▸ RDC) HD

/-- Two computation children with a shared output satisfy the observation
invariant, even when their original inputs are not literal Pis. -/
theorem CoreFamilyCast.pi_core_domain_readout_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HA : CoreFamilyCast D stage .compute Δ a shared)
    (HB : CoreFamilyCast D stage .compute Δ b shared) : PiCoreDomainReadout D Δ a b := by
  intro Γ A B C E u v w z hΓ hA hB hC hE EΓ RA RB
  have IA := HA.interpret heq hs hl hcon hc hreg hoff hD
  obtain ⟨left, RL, CL⟩ := IA.2 RA
  obtain ⟨right, RR, CR⟩ := HB.commute heq hs hl hcon hc hreg hoff hD RB
  obtain ⟨Γ₀, e, T, hΓ₀, _, ht, EE⟩ := IA.1
  obtain ⟨joined, JL, JR⟩ := hc hΓ₀ ht (EE ▸ CL) (EE ▸ CR)
  obtain ⟨out, PL, PR⟩ := static_structure_pi_join_domains heq hs hΓ hA hB hC hE
    (EΓ ▸ (RL.trans JL.in_static_stage).mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩))
    (EΓ ▸ (RR.trans JR.in_static_stage).mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩))
  exact .compute (EΓ ▸ PL) (EΓ ▸ PR) (.leaf .refl)

/-- The annotation constructor satisfies core-exposed Pi readout using only
the ordinary interpretation of its smaller domain comparison certificate. -/
theorem CoreFamilyCast.pi_core_domain_readout_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : CoreFamilyCast D stage (.compare domainMode) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    PiCoreDomainReadout D (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
  intro Γ₀ X Y Z W v₁ v₂ v₃ v₄ _ _ _ _ _ _ RL RR
  exact (contextual_annotation_consumer_pi_domains heq hs hc hΓ hA hC hb ht
    (fun RA RC => H.forward heq hs hl hcon hc hreg hoff hD RA RC) RL RR).mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩)

/-- At a literal Pi frame the stored domain child supplies every future
domain check. The codomain children are irrelevant for this projection. -/
theorem CoreFamilyCast.pi_core_domain_readout_frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D stage (.compare true) Δ A C) :
    PiCoreDomainReadout D Δ (.forallE A B) (.forallE C E) := by
  intro Γ X Y Z W v₁ v₂ v₃ v₄ _ _ _ _ _ _ RL RR
  obtain ⟨X', Y', EQ, RX, _⟩ := RL.pi_parts (fun H => erased_level_core_no_pi H)
  cases EQ
  obtain ⟨Z', W', EQ, RZ, _⟩ := RR.pi_parts (fun H => erased_level_core_no_pi H)
  cases EQ
  exact (H.forward heq hs hl hcon hc hreg hoff hD RX RZ).mono (Step' := ErasedStaticStructureEtaExpansionUnion D) (fun H => ⟨stage, H⟩)

/-- The old recursive core fragment has core-exposed Pi domain readout.
Its full-core interpretation embeds at stage zero, where extraction is proved. -/
theorem LevelRecursiveGuard.pi_core_domain_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b) : PiCoreDomainReadout D Δ a b := by
  intro Γ A B C E u v w z hΓ hA hB hC hE EΓ RA RB
  have HP : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))
      (.forallE (proofErase Γ C) (proofErase (C :: Γ) E)) :=
    ((H.forward hs hl hcon hc RA RB).scoped (fun H => .base (.inl H))).joint.computed
  have HD := stage_zero_computed_pi_domains_compare heq hs hΓ hA hB hC hE .refl .refl HP
  exact EΓ ▸ HD.common.mono (fun H => ⟨0, H⟩)

/-- A lambda cannot expose a Pi through ordinary core computation, so it
cannot create a domain-extraction obligation in either lambda comparison case. -/
theorem PiCoreDomainReadout.left_lambda : PiCoreDomainReadout D Δ (.lam A b) c := by
  intro Γ X Y Z W v₁ v₂ v₃ v₄ _ _ _ _ _ _ RL _
  obtain ⟨_, _, EQ, _, _⟩ := RL.level_core_lam_inv
  cases EQ

/-- The remaining prior-guard case: earlier cast and annotation certificates
must retain domains at typed core-exposed Pi endpoints. The recursive core
subfragment is proved above; coverage of all ContextualCastGuard constructors
is still required. This is not asserted to be smaller than the full front. -/
def CoreFamilyPiPrior (D : Definitions) : Prop :=
  ∀ {stage mode Δ a b}, ContextualCastGuard D stage mode Δ a b → PiCoreDomainReadout D Δ a b

/-- The remaining weakening case, restricted to actual recursive comparison
certificates. The current invariant observes typed Pis only in the requested
context; transporting it must not assume their unproved lower typings. -/
def CoreFamilyPiWeakening (D : Definitions) : Prop :=
  ∀ {Γ Γ' count k stage mode a b}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN count k Γ Γ' → CoreFamilyCast D stage (.compare mode) (proofEraseCtx Γ) a b →
    PiCoreDomainReadout D (proofEraseCtx Γ) a b →
    PiCoreDomainReadout D (proofEraseCtx Γ') (a.liftN count k) (b.liftN count k)

/-- Every other recursive comparison constructor preserves the readout
invariant. The two explicit case hypotheses are not proved here and no strict
smallness or general strong-derivation coverage follows from this reduction. -/
theorem CoreFamilyCast.pi_core_domain_readout_of_cases
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hprior : CoreFamilyPiPrior D) (hweak : CoreFamilyPiWeakening D)
    (H : CoreFamilyCast D stage kind Δ a b) :
    match kind with
    | .compute => True
    | .compare _ => PiCoreDomainReadout D Δ a b := by
  induction H with
  | prior H => exact hprior H
  | core | castConsumer | trans => trivial
  | join HA HB _ _ => exact HA.pi_core_domain_readout_join heq hs hl hcon hc hreg hoff hD HB
  | annotation hΓ hA hC hb ht H _ =>
    exact H.pi_core_domain_readout_annotation heq hs hl hcon hc hreg hoff hD hΓ hA hC hb ht
  | lamCommon | lamSorted => exact PiCoreDomainReadout.left_lambda
  | forallSorted _ _ _ _ HA _ _ _ =>
    exact HA.pi_core_domain_readout_frame heq hs hl hcon hc hreg hoff hD
  | prefixes HA HB _ _ _ ih => exact ih.prefixes heq hs hl hcon hc hreg hoff hD HA HB
  | reducts _ RA RB ih => exact ih.reducts RA RB
  | symm _ ih => exact ih.symm
  | @raise n m kind Δ a b _ _ ih => cases kind <;> exact ih
  | @weaken Γ Γ' count k stage kind a b hΓ hΓ' W H ih =>
    cases kind with
    | compute => trivial
    | compare mode => exact hweak hΓ hΓ' W H ih

end Lean4Lean.VEnv.Strengthening
