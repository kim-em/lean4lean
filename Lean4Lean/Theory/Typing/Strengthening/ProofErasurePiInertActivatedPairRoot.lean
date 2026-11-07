import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertActivatedPairProgress

/-! # Reach an actual native root from an activated pair below a telescope

Component histories lower only the independently typed first field. Its
reserved charge grows by exactly that history's count. A frame/application
rank prevents retained-terminal refocusing from repeating indefinitely.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions} {field : ProofShape}

/-- A full activated-pair minimum with an optional selected application
witness. Competing paths remain unrestricted in either mode. -/
def PiInertActivatedPairMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ K n cb ck endpoint, TypedSource (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) endpoint ∧
    PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K endpoint ck frames ∧ cb+ck = cost ∧
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) tail →
      K tail k → cost ≤ j+k) ∧
    (application = true → PiInertProjectionApplicationRun D Ω family 0 out
      (controls ++ Ω) K endpoint ck frames)

/-- Ordinary full-pair minima enter the frame mode without another premise. -/
theorem PiInertActivatedPairMinimum.of_frame
    (H : PiInertProjectionFrameMinimum D Ω family 0 out (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) cost frames) :
    PiInertActivatedPairMinimum D Ω family info out field controls value cost frames false := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM, by intro E; cases E⟩

/-- An actual application-bearing minimum enters the application mode. -/
theorem PiInertActivatedPairMinimum.of_application
    (H : PiInertProjectionApplicationMinimum D Ω family 0 out (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) cost frames) :
    PiInertActivatedPairMinimum D Ω family info out field controls value cost frames true := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, RB, HK.forget, hc, HM, fun _ => HK⟩

/-- A selected native function/structure root at a prefix of a full activated
pair, with its actual remaining path and unrestricted whole-source minimum.
The lower first-field history is reserved outside this root budget. Reading
the native target through its remaining continuation is still missing. -/
def PiInertActivatedPairRootMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ stage pre pending target endpoint ct ck K,
    pre ++ pending = [field.liftN controls.length, value] ∧
    TypedSource (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    PiInertStage D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    ConstructorEtaBodyRoot D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    ScopedComputeCount (PiInertStage D stage) ct (controls ++ Ω) (ProofShape.mkApps target pending) endpoint ∧
    PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K endpoint ck frames ∧ 1+ct+ck = cost ∧
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) tail →
      K tail k → cost ≤ j+k) ∧
    (application = true → PiInertProjectionApplicationRun D Ω family 0 out
      (controls ++ Ω) K endpoint ck frames)

/-- Below a least failed projection budget, component computation cannot end
at the observer. It either reaches a selected native root or strictly decreases
the frame/application rank, preserving the same original field history and
its joint strict budget. -/
theorem PiInertActivatedPairMinimum.root_or_progress
    (HFail : PiInertPairProjectionBudgetFailure D Ω family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HTfield : TypedSource Ω field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Ω original field)
    (H : PiInertActivatedPairMinimum D Ω family info out field controls value cost frames application)
    (hbudget : charge+cost < budget) :
    (∃ short slot later charge' smaller, TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧ charge'+smaller < budget ∧ smaller ≤ cost ∧
      PiInertActivatedPairRootMinimum D Ω family info out short controls slot smaller frames application) ∨
    (∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Ω short ∧ ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧
      charge'+smaller < budget ∧ smaller ≤ cost ∧
      2*nextFrames + (if nextApplication then 0 else 1) < 2*frames + (if application then 0 else 1) ∧
      PiInertActivatedPairMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM, HApp⟩ := H
  rcases RB.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, values, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, pending, target, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    obtain ⟨short, slot, cf, cv, hsplit, HTshort, RS, EValues⟩ :=
      pi_inert_activated_pair_component_descent heq hs HTfield HT HA
    have RShort := (RField.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage n))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage n)))
    have HTend := HT.pi_inert_compute heq hs RB.forget
    rw [EValues] at RB HK HApp HTend
    cases application with
    | true =>
      obtain ⟨nextControls, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩ :=
        (HApp rfl).activated_pair_next_minimum heq hs hi hp hf hz RB (by simpa only [hc] using HM)
      exact .inr ⟨short, nextControls, nextValue, _, charge+cf, smaller, nextFrames, false,
        HTshort, RShort, by omega, by omega, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, .of_frame HNext⟩
    | false =>
      rcases HK.activated_pair_next_minimum heq hs hi hu hp hf hz hshape hout hproj RB
        (by simpa only [hc] using HM) with
        ⟨EC, later, RO⟩ | ⟨nextControls, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩ |
        ⟨nextControls, smaller, hlen, hsmall, HNext⟩
      · subst controls
        have HTpair : TypedSource Ω (ProofShape.mkApps (.const info.ctorName []) [short, slot]) := by
          simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HTend
        obtain ⟨last, j, hj, RJ⟩ := HLeast.readout_below HTpair RO (by omega)
        have RAll := (RShort.mono (pi_inert_stage_mono (Nat.le_max_left (max fieldStage n) last))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right (max fieldStage n) last)))
        exact (HFail.2.2 _ _ (by omega) RAll).elim
      · exact .inr ⟨short, nextControls, nextValue, _, charge+cf, smaller, nextFrames, false,
          HTshort, RShort, by omega, by omega, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, .of_frame HNext⟩
      · exact .inr ⟨short, nextControls, slot, _, charge+cf, smaller, frames, true,
          HTshort, RShort, by omega, by omega, by simp, .of_application HNext⟩
  · cases HL
    obtain ⟨short, slot, cf, cv, hsplit, HTshort, RS, EArgs⟩ :=
      pi_inert_activated_pair_component_descent heq hs HTfield HT HA
    have RShort := (RField.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage n))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage n)))
    have HSorted := HK.forget.pair_sorted hi hu hp hshape
    have HRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi)
      hD HT RP HR HN RT HSorted hout hproj (cost := cost) (by omega) HM
    have HTroot := HT.pi_inert_compute heq hs RP.forget
    rw [EArgs] at HTroot
    refine .inl ⟨short, slot, _, charge+cf, 1+ct+ck, HTshort, RShort, by omega, by omega,
      n, pre, pending, target, endpoint, ct, ck, K, EArgs, HTroot, HR, HRoot, RT, HK, rfl, ?_, HApp⟩
    intro later j tail k RJ RK
    have RJ' : ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) tail := EArgs ▸ RJ
    have RAlt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ'.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ tail k RAlt RK
    omega

/-- Under a least failed budget, an activated full pair below any retained
telescope reaches a selected native function/structure root. Strong induction
on the frame/application rank removes every component-only transition and
every retained-terminal refocusing. The original lower-field computation and
remaining root minimum retain their joint strict budget. Native-root readout
itself is not asserted. -/
theorem PiInertActivatedPairMinimum.native_root
    (HFail : PiInertPairProjectionBudgetFailure D Ω family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HTfield : TypedSource Ω field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Ω original field)
    (H : PiInertActivatedPairMinimum D Ω family info out field controls value cost frames application)
    (hbudget : charge+cost < budget) :
    ∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Ω short ∧ ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧
      charge'+smaller < budget ∧
      PiInertActivatedPairRootMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication := by
  generalize hrank : 2*frames + (if application then 0 else 1) = rank
  induction rank using Nat.strongRecOn generalizing field controls value cost frames application fieldStage charge with
  | ind rank ih =>
    rcases H.root_or_progress HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTfield RField hbudget with
      ⟨short, slot, later, charge', smaller, HTshort, RShort, hsmall, hcost, HRoot⟩ |
      ⟨short, nextControls, slot, later, charge', smaller, nextFrames, nextApplication,
        HTshort, RShort, hsmall, hcost, hnext, HNext⟩
    · exact ⟨short, controls, slot, later, charge', smaller, frames, application, HTshort, RShort, hsmall, HRoot⟩
    · exact ih _ (by omega) HTshort RShort HNext hsmall rfl

/-- The actual global empty-prefix cut below a least failed pair budget now
reaches a selected native root in either phase: function/structure eta after
activation, or structure eta before the distinguished supply. Component-only
activated tails and repeated function-eta steps in the fresh-pair phase are
eliminated by the two proved inductions. Both outcomes retain the original
field charge plus remaining minimum strictly below the same failure budget.
Native readout across these two phase-specific roots remains open. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_weighted_native_root
    (HFail : PiInertPairProjectionBudgetFailure D Δ family info field value out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTfield : TypedSource Δ field)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (ROuter : ScopedArgumentsCount (PiInertStage D n) Δ outerCost [field, value] args)
    (houter : outerCost ≤ cp)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (REta : PiInertStage D n Δ (.const info.ctorName [])
      (.lam A (.app (.const info.ctorName []) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args major ct
      (ConstructorEtaBodyRoot D))
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    (∃ short controls nextValue later charge smaller nextFrames application,
      TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D later) charge Δ field short ∧
      charge+smaller < budget ∧
      PiInertActivatedPairRootMinimum D Δ family info out short controls nextValue smaller nextFrames application) ∨
    (∃ x charge controls nextValue smaller nextFrames,
      TypedSource Δ x ∧ ScopedComputeCount (PiInertStage D n) charge Δ field x ∧
      charge+smaller < budget ∧
      PiInertFreshPairStructureMinimum D Δ family info out A x controls nextValue smaller nextFrames) := by
  obtain ⟨x, charge, HTx, RField, HNext⟩ := H.empty_pair_prefix_function_eta_eliminate
    heq hs hi hu hp hf hz hshape hD hout hproj SD RN HTfield HT ROuter houter RP REta HK hcost HM
  rcases HNext with ⟨telescope, nextValue, smaller, nextFrames, hsmall, HNext⟩ |
    ⟨controls, nextValue, smaller, nextFrames, hsmall, HNext⟩
  · have HActivated : PiInertActivatedPairMinimum D Δ family info out x telescope nextValue smaller nextFrames false :=
      .of_frame HNext
    exact .inl (HActivated.native_root HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTx RField hsmall)
  · exact .inr ⟨x, charge, controls, nextValue, smaller, nextFrames, HTx, RField, hsmall, HNext⟩

end Lean4Lean.VEnv.Strengthening
