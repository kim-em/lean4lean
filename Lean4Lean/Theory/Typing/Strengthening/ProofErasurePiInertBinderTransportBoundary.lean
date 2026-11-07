import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSortedTransportInduction

/-! # Ground type transport does not construct a core binder world

The function-type congruence case changes its domain binder. Core worlds
permit exactly ordinary core joins at this binder, even though their native
certificates are phrased as interpreted stage-zero computations. A unit and
its certified Eq probe have full carrier transport and actual context
conversion but fail this stronger requirement. Thus existing world movement
cannot by itself discharge the general function-type case.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- Interpreted stage-zero computation has an ordinary-core join to its
specified target, including the retained core tail at the output. -/
theorem PiInertInterpret.zero_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ a)
    (H : PiInertInterpret D 0 .compute Δ a b) :
    ComputeJoin (ErasedLevelCore D) a b := by
  obtain ⟨out, RA, RB⟩ := H.2 .refl
  obtain ⟨shared, RS, RO⟩ := RA.pi_inert_zero_core_join heq hs hc HT
  exact ⟨shared, RS, RB.trans RO⟩

/-- Every core-world lookup forces a genuine ordinary-core join of its two
native annotations. A positive-stage transport certificate cannot replace it. -/
theorem PiInertCoreWorld.lookup_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (W : PiInertCoreWorld D Δ Λ σ) (HT : TypedSource Δ (contextOracle Δ i)) :
    ∃ j, σ i = .bvar j ∧ ComputeJoin (ErasedLevelCore D)
      ((contextOracle Δ i).subst σ) (contextOracle Λ j) := by
  obtain ⟨j, Ej, HL, _⟩ := W.lookup i
  exact ⟨j, Ej, HL.base.zero_core_join heq hs hc (HT.subst W.typed)⟩

/-- For actual equal binder types, an identity core world exists exactly
when their erasures have an ordinary-core join. Ordinary context conversion
supplies typing but does not imply this additional computation property. -/
theorem PiInertCoreWorld.defeq_binder_iff_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A B (.sort u)) :
    PiInertCoreWorld D (proofEraseCtx (A::Γ)) (proofEraseCtx (B::Γ)) ProofShape.Subst.id ↔
      ComputeJoin (ErasedLevelCore D) (proofErase Γ A) (proofErase Γ B) := by
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have hΓB : OnCtx (B::Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.2⟩
  have WT : ContextSubstitution (proofEraseCtx (A::Γ)) (proofEraseCtx (B::Γ))
      ProofShape.Subst.id := ContextSubstitution.of_defeqCtx hΓ (.succ .zero HE)
  constructor
  · intro W
    obtain ⟨j, Ej, J⟩ := W.lookup_core_join heq hs hc (typed_context_oracle_source heq hΓA 0)
    have E : j = 0 := (ProofShape.bvar.inj Ej).symm
    subst j
    simp only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons] at J
    have R := J.subst (fun H => erased_level_core_subst H) (σ := .one .proof)
    simpa only [ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using R
  · intro J
    refine ⟨WT, ?_⟩
    intro i
    have HL := (typed_context_oracle_source heq hΓA i).subst WT
    have HR := typed_context_oracle_source heq hΓB i
    have K : ComputeJoin (ErasedLevelCore D)
        ((contextOracle (proofEraseCtx (A::Γ)) i).subst ProofShape.Subst.id)
        (contextOracle (proofEraseCtx (B::Γ)) i) := by
      cases i with
      | zero =>
        obtain ⟨shared, RA, RB⟩ := J
        simpa only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons]
          using (show ComputeJoin (ErasedLevelCore D)
            ((proofErase Γ A).liftN 1) ((proofErase Γ B).liftN 1) from
              ⟨shared.liftN 1, RA.liftN (fun H => level_lift H),
                RB.liftN (fun H => level_lift H)⟩)
      | succ i =>
        simp only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons]
        exact .refl
    exact ⟨i, rfl, PiInertEvidence.of_core_join hc HL HR K,
      PiInertEvidence.of_core_join hc HR HL K.symm⟩

/-- Certified index histories give full unit/probe carrier transport and a
typed identity context conversion, but no core world for that same binder
change. The index evidence is retained, so this is not the earlier failure
caused by dropping the Eq indices altogether. -/
theorem PiInertFiniteHistory.unit_probe_not_core_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
      (proofErase Γ P) (proofErase Γ Q)) :
    let T := eqTypeProbe u (.const family ls) P Q q
    PiInertGroundTypeEquiv D Γ (.const family ls) T ∧
      ContextSubstitution (proofEraseCtx (.const family ls :: Γ)) (proofEraseCtx (T :: Γ))
        ProofShape.Subst.id ∧
      ¬ PiInertCoreWorld D (proofEraseCtx (.const family ls :: Γ)) (proofEraseCtx (T :: Γ))
        ProofShape.Subst.id := by
  dsimp only
  have HE := eqTypeProbe_defeq heq hΓ hS hP hQ hq
    (H.actual_defeq heq hs hc hΓ hP hQ).toU
  refine ⟨.of_carrier (H.unit_probe_transport heq hs hl hcon hc hreg hoff hRec
    hi hp hx hf (hRigid (henv.projectionRigid hi)) hΓ hS hP hQ hq),
    ContextSubstitution.of_defeqCtx hΓ (.succ .zero HE.symm), ?_⟩
  intro W
  have J := (PiInertCoreWorld.defeq_binder_iff_join heq hs hc hΓ HE.symm).1 W
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  have HX : CarrierExposure (proofErase Γ (.const family ls)) := by
    rw [ES]
    exact .record (ps := []) hi hx hp.symm
  exact eq_rec_no_level_core_carrier_join heq hs hl hcon hreg hoff hRec hRigid hΓ
    (eqTypeProbe_typed heq hΓ hS hP hQ hq) J.symm HX

omit [Params] in
/-- The actual environment core already exhibits the failure with reflexive
proposition indices and an explicitly constructed Eq.refl major. Both the
strong domain equality and its ground transport are supplied, not assumed.
The unit and proposition need only have ordinary typings in the given context. -/
theorem EnvironmentCore.reflexive_probe_binder_boundary
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ family info ls u P}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.const family ls) (.sort u) →
      env.HasType U Γ P (.sort .zero) →
      let T := eqTypeProbe u (.const family ls) P P
        (eqReflApp (.succ .zero) (.sort .zero) P)
      (∃ k, StrongBounded env U k Γ (.const family ls) T (.sort u)) ∧
        PiInertGroundTypeEquiv definitions Γ (.const family ls) T ∧
        ContextSubstitution (proofEraseCtx (.const family ls :: Γ)) (proofEraseCtx (T :: Γ))
          ProofShape.Subst.id ∧
        ¬ PiInertCoreWorld definitions (proofEraseCtx (.const family ls :: Γ))
          (proofEraseCtx (T :: Γ)) ProofShape.Subst.id := by
  letI := henv.params U
  intro Γ family info ls u P heq hi hp hx hf hΓ hS hP
  dsimp only
  have hq := HasType.eqReflApp heq (by trivial)
    (HasType.sort (show VLevel.zero.WF U by trivial)) hP
  have HE := eqTypeProbe_defeq heq hΓ hS hP hP hq hP.toU
  obtain ⟨k, K⟩ := strong_has_bound (HE.symm.strong henv.orderedStrong hΓ)
  refine ⟨⟨k, K⟩, ?_⟩
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    typed_level_core_confluence (fun H => H)
  have index : PiInertFiniteHistory definitions (proofEraseCtx Γ)
      (proofErase Γ (.sort .zero)) (proofErase Γ P) (proofErase Γ P) :=
    PiInertFiniteHistory.refl hc ⟨Γ, P, _, hΓ, rfl, hP, rfl⟩
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  exact index.unit_probe_not_core_binder heq sound (levelCompatible (fun H => H))
    (fun H => H) hc hreg (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
    (fun hrig => no_rigid hrig) hi hp hx hf hΓ hS hP hP hq

/-- Reinterpreting a full finite certificate under actual context conversion
does work: its stage can be selected again after the new typed substitution.
This is not movement of a single local WorldHistory through a non-core world.
Endpoints here are raw shapes and remain literally unchanged. -/
theorem PiInertFiniteHistory.defeq_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HC : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (H : PiInertFiniteHistory D (proofEraseCtx Γ₁) T a b) :
    PiInertFiniteHistory D (proofEraseCtx Γ₂) T a b := by
  intro Λ σ W
  exact H (ContextSubstitution.comp (ContextSubstitution.of_defeqCtx hΓ HC) W)

end Lean4Lean.VEnv.Strengthening
