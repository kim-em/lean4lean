import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertActivatedPairRoot

/-! # Eliminate eta after the activated first field

Opening the one-field function prefix preserves the independently scoped
first field and strictly lowers primitive cost. This combines with the
component frame/application rank, leaving empty-prefix function eta and
saturated structure eta as the selected native boundaries.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private closed_pair_no_function_eta
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshPairRootProgress
variable [Params] {D : Definitions} {field : ProofShape}

/-- An actual eta origin supplies a smaller projection minimum with exactly
one additional frame. Both retained and consumed lambda branches preserve
the final observer, including when the eta is above an intermediate context. -/
theorem CountedEtaFrameOrigin.projection_frame_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaFrameOrigin D n Δ f A u args endpoint ct ck cost K)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K endpoint ck frames) :
    ∃ smaller, smaller < cost ∧ PiInertProjectionFrameMinimum D Ω family index out (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) smaller (frames+1) := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, cd, cb, m, _, _, EO, _, _, RD, HT, RB, hsmall, HM⟩ |
    ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, _, _, _, _, _, HT, RB, WI, HTnext, RS, hsmall, HM⟩
  · have HR : PiInertProjectionRunFrames D Ω family index out Δ K
        (ProofShape.mkApps (.lam A' body') args') ck frames := by simpa only [EO] using HK
    refine ⟨cb+ck, hsmall, (fun body k => K (ProofShape.mkApps (.lam A' body) args') k),
      m, cb, ck, body', HT, RB, ?_, rfl, HM⟩
    exact .retained (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HR
  · have RT : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') endpoint := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have Hnext : TypedSource Δ (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    refine ⟨cb+(cs+ck), by omega, PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HT, RB, ?_, rfl, ?_⟩
    · exact .application (HT.pi_inert_compute heq hs RB.forget) (.inst WI) Hnext RT HK
    · intro later j tail k RJ RK
      have HH := HM later j tail k RJ RK
      omega

/-- The remaining activated native boundary is either function eta on the
empty constructor prefix or structure eta at the full pair. The actual
selected path and unrestricted minimum are retained. Reading either native
target across its continuation remains open. -/
def PiInertActivatedPairBoundaryMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ stage pre pending target endpoint ct ck K,
    pre ++ pending = [field.liftN controls.length, value] ∧
    TypedSource (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    PiInertStage D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    ((pre = [] ∧ ∃ guardStage, guardStage < stage ∧
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

/-- Every activated native root is already at the remaining boundary or eta
opens its supplied first-field prefix, giving a smaller full-pair minimum.
The first field remains the literal lift of the SAME observer-scope field. -/
theorem PiInertActivatedPairRootMinimum.supplied_eta_progress
    (H : PiInertActivatedPairRootMinimum D Ω family info out field controls value cost frames application)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0) :
    PiInertActivatedPairBoundaryMinimum D Ω family info out field controls value cost frames application ∨
    (∃ A u smaller, smaller < cost ∧
      PiInertActivatedPairMinimum D Ω family info out field (A :: controls) (etaArgument u)
        smaller (frames+1) false) := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR, HRoot, RT, HK, hc, HM, HApp⟩ := H
  obtain ⟨guardStage, hg, HE⟩ := HRoot
  have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D guardStage) :=
    erased_static_structure_eta_expansion_stage_descent heq hs guardStage
  have HTwhole : TypedSource (controls ++ Ω)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [← ProofShape.mkApps_append, EArgs] using HT
  rcases HE with HE | HE
  · cases pre with
    | nil =>
      exact .inl ⟨stage, [], pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
        .inl ⟨rfl, guardStage, hg, HE⟩, RT, HK, hc, HM, HApp⟩
    | cons first rest =>
      have EF : first = field.liftN controls.length := (List.cons.inj EArgs).1
      subst first
      have ER : rest ++ pending = [value] := (List.cons.inj EArgs).2
      cases HE with
      | intro RN SD =>
        rename_i A B u
        cases rest with
        | nil =>
          have RP : ScopedComputeCount (PiInertStage D stage) 0 (controls ++ Ω)
              (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value])
              (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length]) pending) := by
            rw [← ProofShape.mkApps_append, EArgs]
            exact .beta BetaRed.refl
          have HO := pi_inert_eta_frame_origin heq hs hguard HTwhole RN SD RP HR RT
            HK.forget.holds (cost := cost) (by omega) HM
          obtain ⟨smaller, hsmall, HNext⟩ := HO.projection_frame_minimum heq hs HK
          apply Or.inr
          refine ⟨A, u, smaller, hsmall, PiInertActivatedPairMinimum.of_frame ?_⟩
          simpa only [ProofShape.liftN_mkApps, ProofShape.liftN, List.map_cons, List.map_nil,
            ProofShape.mkApps, List.length_cons, List.cons_append, ProofShape.liftN_add, Nat.add_comm] using HNext
        | cons second tail =>
          have ES : second = value := (List.cons.inj ER).1
          have ET : tail ++ pending = [] := (List.cons.inj ER).2
          have hlen := congrArg List.length ET
          have ET' : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append, List.length_nil] at hlen; omega)
          have EP : pending = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append, List.length_nil] at hlen; omega)
          subst second tail pending
          exact (closed_pair_no_function_eta hguard hi hp hf hz HT RN).elim
  · have EP := TypedSource.structure_eta_pending_nil hguard HTwhole HE
    exact .inl ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
      .inr ⟨EP, guardStage, hg, HE⟩, RT, HK, hc, HM, HApp⟩

/-- Repeated function eta after the supplied first field and all component
transitions terminate by primitive cost followed by frame/application rank.
The remaining selected native root is empty-prefix function eta or saturated
structure eta, and its budget still includes the original lower-field history. -/
theorem PiInertActivatedPairMinimum.function_eta_eliminate
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
      PiInertActivatedPairBoundaryMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication := by
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
        · exact ⟨short, controls, slot, later, charge', smaller, frames, application,
            HTshort, RShort, hsmall, HBoundary⟩
        · exact costIH nextCost (by omega) HTshort RShort HNext (by omega)
      · by_cases hstrict : smaller < cost
        · exact costIH smaller hstrict HTshort RShort HNext hsmall
        · have E : smaller = cost := by omega
          subst smaller
          exact rankIH _ (by omega) HTshort RShort HNext hsmall rfl

/-- The actual global empty-prefix cut reaches a weighted native boundary:
empty-prefix function eta or saturated structure eta after activation, or
structure eta before the distinguished supply. Supplied-prefix function eta
and component-only transitions have been eliminated, while all competing
paths and the original field charge remain unrestricted. Native readout at
these boundaries is the remaining obligation. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_weighted_eta_boundary
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
      PiInertActivatedPairBoundaryMinimum D Δ family info out short controls nextValue smaller nextFrames application) ∨
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
    exact .inl (HActivated.function_eta_eliminate HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTx RField hsmall)
  · exact .inr ⟨x, charge, controls, nextValue, smaller, nextFrames, HTx, RField, hsmall, HNext⟩


end Lean4Lean.VEnv.Strengthening
