import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertIntermediateSupplyBoundary

/-! # Consume constructor eta before an arbitrary projection continuation

The final sorted observer excludes administrative body roots even when the
current endpoint is a lambda spine. An unconsumed eta is retained with its
exact function and argument computations; consumption gives the existing
counted native body cut without any local non-lambda assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private eta_argument_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut
variable [Params] {D : Definitions}

/-- At a constructor eta minimum with an arbitrary sorted projection tail,
either the eta remains as the exact computed lambda spine or the actual
consuming beta gives a counted native body cut. The latter branch permits
lambda-spine endpoints: administrative roots are excluded by replaying the
whole sorted continuation. Readout of the retained branch remains open. -/
theorem pi_inert_constructor_eta_body_cut_or_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hRigid : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const c ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const c ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))) args) endpoint)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ original tail →
      K tail k → cost ≤ j+k) :
    (∃ A' body' args' cf ca, cf+ca = ct ∧
      endpoint = ProofShape.mkApps (.lam A' body') args' ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args args') ∨
    CountedEtaBodySpineCut D n Δ c ls pre A u args endpoint ct (ConstructorEtaBodyRoot D) := by
  have hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ original endpoint → cp+1+ct ≤ j := by
    intro later j RJ
    have HH := HM later j endpoint ck RJ HK.forget.holds
    omega
  have HOuter := HR
  rcases RT.pi_inert_lambda_spine_or_beta with ⟨A', b', args', cf, ca, hc, EO, RF, RX⟩ |
      ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · have RAll := RP.trans (((ScopedComputeCount.base HR).trans RF).mkApps RX)
    have HH := HM n _ endpoint ck (by simpa only [EO] using RAll) HK.forget.holds
    exact .inl ⟨A', b', args', cf, ca, by omega, EO, RF, RX⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    have RBspine : ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (ProofShape.mkApps (.const c ls) (pre.map (·.liftN 1) ++ [etaArgument u])) body' := by
      simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RB
    obtain ⟨hexact, _, hminBody⟩ := pi_inert_counted_lambda_body_minimal
      RP HR RD RB RX RS (by omega) hmin
    obtain ⟨_, hminContinuation⟩ := pi_inert_counted_lambda_continuation_minimal
      RP HR RD RB RX RS (by omega) hmin
    obtain ⟨_, _, HJoint⟩ := pi_inert_counted_lambda_continuation_minimal_of
      RP HR RD RB RX RS HK.forget.holds (cost := cost) (by omega) HM
    have hcExact : cf+ca+cs = ct := by omega
    rcases RBspine.const_spine_components_or_cut_counted (U := univs) with
      ⟨ls', rawArgs, ch, cc, hcomponents, EO, _, RH, RA⟩ |
      ⟨ls', bodyPre, bodyPending, target, pb, tb, pa, hcut, hpa, HL, HA, RPB, HR, HN, RTB⟩
    · obtain ⟨pre', slot', cp', cx', rfl, hargs, Rpre, Rslot⟩ := RA.snoc_inv
      obtain rfl := eta_argument_fixed Rslot.forget
      have RG : ScopedComputeCount (PiInertStage D m) (ch+cp') (A :: Δ)
          ((ProofShape.mkApps (.const c ls) pre).liftN 1) (ProofShape.mkApps (.const c ls') pre') := by
        simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using RH.mkApps Rpre
      have EB : body' = .app (ProofShape.mkApps (.const c ls') pre') (etaArgument u) := by
        simpa only [ProofShape.mkApps_snoc] using EO
      have RR := pi_inert_retained_eta_body_count_bypass heq hs hguard HT RN SD RG RX (EB ▸ RS)
      have HM := hmin _ _ ((RP.mono (pi_inert_stage_mono (Nat.le_max_right m n))).trans RR)
      omega
    · have hcutExact : pb+1+tb = cb := by
        have RT' := ((ScopedComputeCount.base HR).mkApps ScopedArgumentsCount.refl).trans RTB
        rw [← ProofShape.mkApps_append] at RT'
        have R := RPB.trans RT'
        have HM := hminBody m (pb+1+tb) (by
          simpa only [Nat.add_zero, ← Nat.add_assoc,
            ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using R)
        omega
      have RPB' : ScopedComputeCount (PiInertStage D m) pb (A :: Δ)
          (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))
          (ProofShape.mkApps (.const c ls') (bodyPre ++ bodyPending)) := by
        simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RPB
      obtain ⟨HTbody, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
      have HTroot := RPB'.forget.spine_cut_source_typed
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs m)) HTbody
      have HTlong := HT.pi_inert_compute heq hs
        ((ScopedComputeCount.base HOuter).mkApps (ScopedArgumentsCount.refl (args := args))).forget
      have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
          (ProofShape.mkApps (.lam A' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
        simpa only [ProofShape.mkApps] using
          (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
            (ScopedArgumentsCount.refl (args := xs'))
      have HTnext := HTlong.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
      have HApp : PiInertSortedProjectionContinuationRun D Ω family index out observerSort (A :: Δ)
          (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K) body' (cs+ck) :=
        .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WI)
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
      have RPBwhole : ScopedComputeCount (PiInertStage D m) pb (A :: Δ)
          (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))
          (ProofShape.mkApps (ProofShape.mkApps (.const c ls') bodyPre) bodyPending) := by
        simpa only [ProofShape.mkApps_append] using RPB'
      have HTtarget := (HTbody.pi_inert_compute heq hs RPBwhole.forget).pi_inert_compute heq hs
        ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).forget
      have HD := pi_inert_sorted_frames_minimum_no_administrative heq hs HTtarget RPBwhole RTB HApp
        hout hproj (cost := cb+cs+ck) (by omega) HJoint
      apply Or.inr
      apply CountedEtaBodySpineCut.constructor_roots heq hRigid hD
      refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending,
        target, pb, tb, hcExact, hsplit, hcutExact, RF, RX, RS, RD, HL,
        ⟨HA.forget, pa, hpa, HA⟩, RPB', HR, HN, RTB,
        hminBody, hminContinuation, ?_, HTroot, WI, ?_, trivial⟩
      · intro Recovery HI
        cases HI with
        | intro _ => exact HD ((AdministrativeHeadDeletion.identity .drop).mkApps bodyPending)
      · intro HC
        cases HC with
        | intro _ => exact HD ((AdministrativeHeadDeletion.constant .drop).mkApps bodyPending)

/-- An actual lambda-spine suffix with no selected consuming beta in its
chosen decomposition. It keeps the exact function and argument paths and
their total primitive count. This is stronger than merely having a lambda
endpoint; a consumed eta may also end at a later lambda. -/
def PiInertRetainedLambdaSpine (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (target : ProofShape) (args : List ProofShape) (endpoint : ProofShape) (ct : Nat) : Prop :=
  ∃ C body fields cf ca, cf+ca = ct ∧ endpoint = ProofShape.mkApps (.lam C body) fields ∧
    ScopedComputeCount (PiInertStage D n) cf Δ target (.lam C body) ∧
    ScopedArgumentsCount (PiInertStage D n) Δ ca args fields

/-- The selected retained constructor history descends independently of its
arguments. Its lower-scope count includes the native root, while the first
field and value still have their exact upper argument-vector history. This
supplies data for commuting the computed head through a later application;
that subsequent progress is not asserted here. -/
theorem PiInertRetainedLambdaSpine.lower_constructor_head
    (H : PiInertRetainedLambdaSpine D n (controls ++ Ω) target args endpoint ct)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Ω (.const ctor levels))
    (HT : TypedSource (controls ++ Ω) source)
    (HR : PiInertStage D n (controls ++ Ω) (.const ctor levels) target) :
    ∃ short C body fields cg ca, TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D n) cg Ω (.const ctor levels) short ∧
      short.liftN controls.length = .lam C body ∧
      endpoint = ProofShape.mkApps (short.liftN controls.length) fields ∧
      ScopedArgumentsCount (PiInertStage D n) (controls ++ Ω) ca args fields ∧ cg+ca = 1+ct := by
  obtain ⟨C, body, fields, cf, ca, hc, EO, RF, RX⟩ := H
  have RHead : ScopedComputeCount (PiInertStage D n) (1+cf) (controls ++ Ω)
      ((ProofShape.const ctor levels).liftN controls.length) (.lam C body) :=
    (ScopedComputeCount.base HR).trans RF
  obtain ⟨short, HTshort, RShort, EShort⟩ :=
    pi_inert_telescope_component_count_descend heq hs HTlower HT RHead
  exact ⟨short, C, body, fields, 1+cf, ca, HTshort, RShort, EShort.symm,
    by simpa only [EShort] using EO, RX, by omega⟩

/-- After eliminating actual consumed eta cuts, the activated function
boundary retains the original eta lambda with exact function/argument paths.
Structure eta remains saturated. Reading the retained computed head through
its actual future application and reading structure targets remain open. -/
def PiInertActivatedPairRetainedBoundaryMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ stage pre pending target endpoint ct ck K,
    pre ++ pending = [field.liftN controls.length, value] ∧
    TypedSource (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    PiInertStage D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    ((pre = [] ∧ PiInertRetainedLambdaSpine D stage (controls ++ Ω) target pending endpoint ct ∧ ∃ guardStage, guardStage < stage ∧
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

/-- Every consumed empty-prefix eta yields strict primitive progress,
even if its selected endpoint is a lambda spine. The only function boundary
kept here is an actual retained decomposition; the exact original field
charge and intermediate structure supply are preserved. -/
theorem PiInertActivatedPairBoundaryMinimum.consumption_progress
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
    PiInertActivatedPairRetainedBoundaryMinimum D Ω family info out field controls value cost frames application ∨
    (∃ short charge later, TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D later) charge Ω field short ∧
      ((∃ nextControls nextValue smaller nextFrames, charge+smaller < cost ∧
        PiInertActivatedPairMinimum D Ω family info out short nextControls nextValue smaller nextFrames false) ∨
       (∃ A Acontrols nextValue smaller nextFrames, charge+smaller < cost ∧
        PiInertFreshPairStructureMinimum D Ω (controls ++ Ω) family info out A
          (short.liftN controls.length) Acontrols nextValue smaller nextFrames))) := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR, HNative, RT, HK, hc, HM, HApp⟩ := H
  rcases HNative with ⟨EP, guardStage, hg, HE⟩ | HStructure
  · subst pre
    have E : pending = [field.liftN controls.length, value] := EArgs
    subst pending
    cases HE with
    | intro RN SD =>
      rename_i A B u
      have RP : ScopedComputeCount (PiInertStage D stage) 0 (controls ++ Ω)
          (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value])
          (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) :=
        .beta BetaRed.refl
      have HSorted := HK.forget.pair_sorted hi hu hp hshape
      have HSplit := pi_inert_constructor_eta_body_cut_or_retained heq hs
        (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
        (henv.projectionCtorRigid hi) hD (pre := []) HT RN SD RP HR RT HSorted hout hproj
        (cost := cost) (by omega) HM
      rcases HSplit with HRetained | HCut
      · exact .inl ⟨stage, [], _, _, endpoint, ct, ck, K, rfl, HT, HR,
          .inl ⟨rfl, HRetained, guardStage, hg, .intro RN SD⟩, RT, HK, hc, HM, HApp⟩
      · obtain ⟨short, charge, HTshort, RShort, HNext⟩ :=
          HCut.empty_pair_prefix_intermediate_progress heq hs hi hu hp hf hz hshape hD hout hproj
            SD RN HTfield HT ScopedArgumentsCount.refl (by omega) RP HR HK (by omega) HM
        refine .inr ⟨short, charge, stage, HTshort, RShort, ?_⟩
        rcases HNext with HNext | ⟨Acontrols, nextValue, smaller, nextFrames, hsmall, HNext⟩
        · exact .inl HNext
        · exact .inr ⟨A, Acontrols, nextValue, smaller, nextFrames, hsmall, HNext⟩
  · exact .inl ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
      .inr HStructure, RT, HK, hc, HM, HApp⟩

/-- Cost/frame induction removes all supplied-prefix eta and all actual
consumed empty-prefix eta, including consumed paths ending at later lambdas.
The residual is retained empty-prefix eta or structure eta in either phase.
The original observer-scope field history remains within the same joint
strict failure budget throughout the induction. -/
theorem PiInertActivatedPairMinimum.consumed_eta_eliminate
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
      PiInertActivatedPairRetainedBoundaryMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication) ∨
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
        · rcases HBoundary.consumption_progress heq hs hi hu hp hf hz hshape hD hout hproj HTshort with
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

/-- The actual global empty-prefix cut now reaches an activated retained
eta/structure boundary or structure eta before an intermediate supply. No
actual consumed eta case remains hidden behind a lambda endpoint. The exact
field charge and strict budget persist; the two remaining kinds of native
readout, and therefore strengthening, are still open. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_weighted_retained_boundary
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
      PiInertActivatedPairRetainedBoundaryMinimum D Δ family info out short nextControls slot smaller nextFrames nextApplication) ∨
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
    exact HActivated.consumed_eta_eliminate HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTx RField hsmall
  · refine .inr ⟨x, [], A, controls, nextValue, n, charge, smaller, nextFrames, HTx, RField, hsmall, ?_⟩
    simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HNext


end Lean4Lean.VEnv.Strengthening
