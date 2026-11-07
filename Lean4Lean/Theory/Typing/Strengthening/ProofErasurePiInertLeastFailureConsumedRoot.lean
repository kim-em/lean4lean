import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertBinderExitMinimum

/-! # A least failure cannot return through a component-only pair body

The original field charge and the actual body/application/observer minimum
share one budget. A component-only body returns that field to a strictly
smaller same-scope pair minimum, contradicting leastness. The remaining first
constructor root is native eta and keeps the weighted original-field invariant.
Further eta descent, including retained frames, remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Analyze a smaller lifted-field pair body consumed into the observer's
scope. Leastness excludes the stable component branch. The actual first root
is function/structure eta, with the same original field and joint budget;
recursive readout after that root is not assumed. -/
theorem PiInertPairProjectionBudgetFailure.consumed_pair_weighted_root
    (H : PiInertPairProjectionBudgetFailure D Δ family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Δ original field)
    (HT : TypedSource (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]))
    (RBody : ScopedComputeCount (PiInertStage D n) cb (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) endpoint)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending) next)
    (HK : PiInertProjectionContinuationRun D Δ family 0 out Δ K next ck)
    (hbudget : charge+cb+cs+ck < budget)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) endpoint' →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K endpoint' k →
      cb+cs+ck ≤ j+k) :
    ∃ pre bodyPending target cp ct ca, cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D n) (A :: Δ) ca
        [field.liftN 1, etaArgument u] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D n) cp (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u])
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D n (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
        (ProofShape.mkApps target bodyPending) endpoint ∧
      PiInertPairWeightedBodyRoot D Δ family info original u out budget n (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) pre) target := by
  rcases pi_inert_consumed_pair_minimum_transfer_or_root heq hs hi hp hf hz SD HTfield HT
      RBody W HNext RNext HK HM with
    ⟨_, short, value', j, hj, HTshort, RF, HMin⟩ |
    ⟨pre, bodyPending, target, cp, ct, ca, hcut, hca, HA, RP, HR, HN, RT, hsmall, HMin⟩
  · have RF' := (RField.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage n))).trans
      (RF.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage n)))
    exact (H.no_smaller_transfer HLeast RF' HMin heq hs hi hp hf hz (by omega) (by omega)).elim
  · have hu := TypedSource.constructor_uvars_zero hi H.1
    have HKfull : PiInertProjectionContinuationRun D Δ family 0 out (A :: Δ)
        (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K) endpoint (cs+ck) :=
      .application (HT.pi_inert_compute heq hs RBody.forget) (.inst W) HNext RNext HK
    have HKS := HKfull.pair_sorted hi hu hp hshape
    have HRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi)
      hD HT RP HR HN RT HKS hout hproj (cost := cb+cs+ck) (by omega) HM
    have HTwhole : TypedSource (A :: Δ)
        (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) bodyPending) := by
      simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
    have HRootMin : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) bodyPending) endpoint' →
        PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K endpoint' k →
        1+ct+(cs+ck) ≤ j+k := by
      intro later j endpoint' k RJ RK
      have RAlt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
        (by simpa only [ProofShape.mkApps_append] using
          RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
      have HH := HM _ _ endpoint' k RAlt RK
      omega
    refine ⟨pre, bodyPending, target, cp, ct, ca, hcut, hca, HA, RP, HR, RT, ?_⟩
    obtain ⟨guardStage, hg, HE | HE⟩ := HRoot
    · exact .inl ⟨guardStage, hg, HE, bodyPending, ct, endpoint, cs+ck, _,
        by omega, HTwhole, HR, RT, HKfull, HRootMin⟩
    · have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D guardStage) :=
        erased_static_structure_eta_expansion_stage_descent heq hs guardStage
      have EP := TypedSource.structure_eta_pending_nil hguard HTwhole HE
      obtain ⟨short, j, hj, HTshort, RF, Efields⟩ :=
        pi_inert_single_field_eta_body_count_ancestry heq hs SD HTfield HA
      rw [EP, List.append_nil] at Efields
      have RF' := (RField.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage n))).trans
        (RF.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage n)))
      exact .inr ⟨guardStage, short, [], max fieldStage n, charge+j, hg, HTshort, RF',
        congrArg (ProofShape.mkApps (.const info.ctorName [])) Efields, HE,
        bodyPending, ct, endpoint, cs+ck, _, by omega, HTwhole, HR, RT, HKfull, HRootMin⟩


/-- Apply the consuming-frame exclusion to an actual smaller pair minimum,
without assuming a frame decomposition. Identity frames are absorbed exactly;
the only alternative left unclassified here is an actual retained lambda frame.
A native root still needs recursive eta readout, and the retained alternative
still needs its later consuming beta to be focused. -/
theorem PiInertPairProjectionBudgetFailure.lifted_pair_minimum_root_or_retained
    (H : PiInertPairProjectionBudgetFailure D Δ family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Δ original field)
    (HMin : PiInertProjectionContinuationMinimum D Δ family 0 out (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) cost)
    (hbudget : charge+cost < budget) :
    (∃ stage pre target, PiInertPairWeightedBodyRoot D Δ family info original u out budget
      stage (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target) ∨
    (∃ n cb ck body A' args domainStage cd v K,
      ScopedComputeCount (PiInertStage D n) cb (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) body ∧
      DomainSort Δ A v ∧ ScopedComputeCount (PiInertStage D domainStage) cd Δ A A' ∧
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id ∧
      PiInertProjectionContinuationRun D Δ family 0 out Δ K (ProofShape.mkApps (.lam A' body) args) ck ∧
      cb+ck = cost ∧
      ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) endpoint' →
        K (ProofShape.mkApps (.lam A' endpoint') args) k → cost ≤ j+k) := by
  have HE := HMin.pair_binder_exit heq hs hi hp hz (by simp [hf])
  cases HE with
  | consumed HT RB W HNext RS HK hcost HM =>
    obtain ⟨pre, bodyPending, target, cp, ct, ca, _, _, _, _, _, _, HG⟩ :=
      H.consumed_pair_weighted_root HLeast heq hs hi hp hf hz hshape hD hout hproj
        SD HTfield RField HT RB W HNext RS HK (by omega) (by simpa only [hcost] using HM)
    exact .inl ⟨_, pre, target, HG⟩
  | retained HT RB SD' RD WI HK hcost HM =>
    exact .inr ⟨_, _, _, _, _, _, _, _, _, _, RB, SD', RD, WI, HK, hcost, HM⟩

end Lean4Lean.VEnv.Strengthening
