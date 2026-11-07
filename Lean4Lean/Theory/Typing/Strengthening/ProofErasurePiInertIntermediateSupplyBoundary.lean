import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertActivatedEtaElimination

/-! # Activated eta boundaries after intermediate supply

The supply base is independent of the final observer. Repeated activated
empty-prefix eta with a non-lambda endpoint now decreases primitive cost.
Only lambda endpoints and structure targets remain as native boundaries.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions} {field : ProofShape}

/-- A selected activated native minimum after eliminating non-lambda
empty-prefix endpoints. The function branch must end at an actual lambda
spine; structure eta remains saturated. Reading these targets across the
continuation is still open. -/
def PiInertActivatedPairLambdaBoundaryMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ stage pre pending target endpoint ct ck K,
    pre ++ pending = [field.liftN controls.length, value] ∧
    TypedSource (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    PiInertStage D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    ((pre = [] ∧ (∃ C b args, endpoint = ProofShape.mkApps (.lam C b) args) ∧ ∃ guardStage, guardStage < stage ∧
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) (controls ++ Ω)
          (ProofShape.mkApps (.const info.ctorName []) pre) target) ∨
      (pending = [] ∧ ∃ guardStage, guardStage < stage ∧
        NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) (controls ++ Ω)
          (ProofShape.mkApps (.const info.ctorName []) pre) target)) ∧
    ScopedComputeCount (PiInertStage D stage) ct (controls ++ Ω) (ProofShape.mkApps target pending) endpoint ∧
    PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K endpoint ck frames ∧ 1+ct+ck = cost ∧
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) tail →
      K tail k → cost ≤ j+k) ∧
    (application = true → PiInertProjectionApplicationRun D Ω family 0 out
      (controls ++ Ω) K endpoint ck frames)

/-- A remaining activated boundary either has a lambda endpoint/structure
root or gives strict primitive progress, preserving a separately lowered
first-field history. The structure alternative retains its intermediate
supplying base explicitly. -/
theorem PiInertActivatedPairBoundaryMinimum.intermediate_supply_progress
    (H : PiInertActivatedPairBoundaryMinimum D Ω family info out field controls value cost frames application)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HTfield : TypedSource Ω field) :
    PiInertActivatedPairLambdaBoundaryMinimum D Ω family info out field controls value cost frames application ∨
    (∃ short charge later, TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D later) charge Ω field short ∧
      ((∃ nextControls nextValue smaller nextFrames, charge+smaller < cost ∧
        PiInertActivatedPairMinimum D Ω family info out short nextControls nextValue smaller nextFrames false) ∨
       (∃ A Acontrols nextValue smaller nextFrames, charge+smaller < cost ∧
        PiInertFreshPairStructureMinimum D Ω (controls ++ Ω) family info out A
          (short.liftN controls.length) Acontrols nextValue smaller nextFrames))) := by
  classical
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR, HNative, RT, HK, hc, HM, HApp⟩ := H
  rcases HNative with ⟨EP, guardStage, hg, HE⟩ | HStructure
  · subst pre
    have E : pending = [field.liftN controls.length, value] := EArgs
    subst pending
    by_cases HL : ∃ C b args, endpoint = ProofShape.mkApps (.lam C b) args
    · exact .inl ⟨stage, [], _, target, endpoint, ct, ck, K, rfl, HT, HR,
        .inl ⟨rfl, HL, guardStage, hg, HE⟩, RT, HK, hc, HM, HApp⟩
    · cases HE with
      | intro RN SD =>
        rename_i A B u
        obtain ⟨short, charge, HTshort, RShort, HNext⟩ :=
          pi_inert_activated_empty_eta_nonlambda_progress heq hs hi hu hp hf hz hshape hD hout hproj
            SD RN HTfield HT HR RT HK (by omega)
            (fun C b args E => HL ⟨C, b, args, E⟩) HM
        refine .inr ⟨short, charge, stage, HTshort, RShort, ?_⟩
        rcases HNext with HNext | ⟨Acontrols, nextValue, smaller, nextFrames, hsmall, HNext⟩
        · exact .inl HNext
        · exact .inr ⟨A, Acontrols, nextValue, smaller, nextFrames, hsmall, HNext⟩
  · exact .inl ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
      .inr HStructure, RT, HK, hc, HM, HApp⟩

/-- Cost/frame induction eliminates every activated function-eta step
except empty-prefix eta whose selected endpoint is a lambda spine. It also
records structure roots before an arbitrary intermediate supply. The exact
original observer-scope field history and strict joint failure budget survive
all iterations; no readout at either remaining boundary is assumed. -/
theorem PiInertActivatedPairMinimum.intermediate_supply_eliminate
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
    (∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Ω short ∧ ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧
      charge'+smaller < budget ∧
      PiInertActivatedPairLambdaBoundaryMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication) ∨
    (∃ short baseControls A Acontrols slot later charge' smaller nextFrames,
      TypedSource Ω short ∧ ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧
      charge'+smaller < budget ∧
      PiInertFreshPairStructureMinimum D Ω (baseControls ++ Ω) family info out A
        (short.liftN baseControls.length) Acontrols slot smaller nextFrames) := by
  induction cost using Nat.strongRecOn generalizing field controls value frames application fieldStage charge with
  | ind cost costIH =>
    generalize hrank : 2*frames + (if application then 0 else 1) = rank
    induction rank using Nat.strongRecOn generalizing field controls value frames application fieldStage charge with
    | ind rank rankIH =>
      rcases H.root_or_progress HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTfield RField hbudget with
        ⟨short, slot, later, charge', smaller, HTshort, RShort, hsmall, hcost, HRoot⟩ |
        ⟨short, nextControls, slot, later, charge', smaller, nextFrames, nextApplication,
          HTshort, RShort, hsmall, hcost, hnext, HNext⟩
      · rcases HRoot.supplied_eta_progress heq hs hi hp hf hz with HBoundary |
          ⟨nextA, nextU, nextCost, hnextCost, HNext⟩
        · rcases HBoundary.intermediate_supply_progress heq hs hi hu hp hf hz hshape hD hout hproj HTshort with
            HLast | ⟨last, extra, lastStage, HTlast, RLast, HNext⟩
          · exact .inl ⟨short, controls, slot, later, charge', smaller, frames, application,
              HTshort, RShort, hsmall, HLast⟩
          · have RAll := (RShort.mono (pi_inert_stage_mono (Nat.le_max_left later lastStage))).trans
              (RLast.mono (pi_inert_stage_mono (Nat.le_max_right later lastStage)))
            rcases HNext with ⟨nextControls, nextValue, nextCost, nextFrames, hnextCost, HNext⟩ |
              ⟨A, Acontrols, nextValue, nextCost, nextFrames, hnextCost, HNext⟩
            · exact costIH nextCost (by omega) HTlast RAll HNext (by omega)
            · exact .inr ⟨last, controls, A, Acontrols, nextValue, _, charge'+extra,
                nextCost, nextFrames, HTlast, RAll, by omega, HNext⟩
        · exact costIH nextCost (by omega) HTshort RShort HNext (by omega)
      · by_cases hstrict : smaller < cost
        · exact costIH smaller hstrict HTshort RShort HNext hsmall
        · have E : smaller = cost := by omega
          subst smaller
          exact rankIH _ (by omega) HTshort RShort HNext hsmall rfl

/-- The actual global empty-prefix cut reaches only an activated lambda
endpoint/structure boundary or a structure root before a possibly intermediate
supply. This composes both phase inductions and preserves the same original
field history plus remaining minimum strictly below the failed budget. The
remaining boundary readouts, hence strengthening itself, are still open. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_weighted_intermediate_boundary
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
    (∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D later) charge' Δ field short ∧
      charge'+smaller < budget ∧
      PiInertActivatedPairLambdaBoundaryMinimum D Δ family info out short nextControls slot smaller nextFrames nextApplication) ∨
    (∃ short baseControls A Acontrols slot later charge' smaller nextFrames,
      TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D later) charge' Δ field short ∧
      charge'+smaller < budget ∧
      PiInertFreshPairStructureMinimum D Δ (baseControls ++ Δ) family info out A
        (short.liftN baseControls.length) Acontrols slot smaller nextFrames) := by
  obtain ⟨x, charge, HTx, RField, HNext⟩ := H.empty_pair_prefix_function_eta_eliminate
    heq hs hi hu hp hf hz hshape hD hout hproj SD RN HTfield HT ROuter houter RP REta HK hcost HM
  rcases HNext with ⟨telescope, nextValue, smaller, nextFrames, hsmall, HNext⟩ |
    ⟨controls, nextValue, smaller, nextFrames, hsmall, HNext⟩
  · have HActivated : PiInertActivatedPairMinimum D Δ family info out x telescope nextValue smaller nextFrames false :=
      .of_frame HNext
    exact HActivated.intermediate_supply_eliminate HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTx RField hsmall
  · refine .inr ⟨x, [], A, controls, nextValue, n, charge, smaller, nextFrames, HTx, RField, hsmall, ?_⟩
    simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HNext

end Lean4Lean.VEnv.Strengthening
