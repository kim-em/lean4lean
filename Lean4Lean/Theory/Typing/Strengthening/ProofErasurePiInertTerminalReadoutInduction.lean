import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedApplicationReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTerminalSupplyCut

/-! # Retained terminal readout with an application witness

An exposed sorted projection must consume its retained lambda. The resulting
body execution has an actual application witness. It may keep the same frame
count, but its application rank is smaller: 2*frames precedes 2*frames+1.
Readout for that body execution gives a competitor for the original terminal.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private rebuild_terminal_body
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTerminalSupplyCut
variable [Params] {D : Definitions}

/-- Ancestry readout at an exact frame count when the selected execution has
an application witness. At equal primitive cost, give this case rank
2*frames, before the unrestricted case at rank 2*frames+1. This is an induction
target; generalized function-root and nested retained-prefix progress remain
open before either target can be proved throughout the least-failure range. -/
def PiInertPairAncestryApplicationReadout (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out : ProofShape) (cost frames : Nat) : Prop :=
  ∀ {Δ field value stage cb endpoint K ck},
    TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
    ScopedComputeCount (PiInertStage D stage) cb Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) endpoint →
    PiInertProjectionApplicationRun D Ω family 0 out Δ K endpoint ck frames →
    cb+ck = cost →
    ∀ {source u lower fieldStage fieldCost},
      ControlTyping Δ (.proj family 0 source) (.sort u) →
      AdministrativeHeadDeletion field lower →
      ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower →
      ∃ later j major k, j+k ≤ fieldCost+cost ∧
        ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k

/-- Unrestricted exact-frame readout includes the application-witness case. -/
theorem PiInertPairAncestryReadoutFrames.application
    (H : PiInertPairAncestryReadoutFrames D Ω family info out cost frames) :
    PiInertPairAncestryApplicationReadout D Ω family info out cost frames := by
  intro Δ field value stage cb endpoint K ck HT R HK hc source u lower fieldStage fieldCost HS HD RF
  exact H HT R HK.forget hc HS HD RF

/-- The zero-frame case is an actual final projection in the observer's
scope. Below the least failed budget it has ancestry readout directly, with
no cost or rank induction hypothesis. The initial pair path is arbitrary. -/
theorem pi_inert_ancestry_readout_zero_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hcost : cost < budget) : PiInertPairAncestryReadoutFrames D Ω family info out cost 0 := by
  intro Δ field value stage cb endpoint K ck HT R HK hc source u lower fieldStage fieldCost HS HD RF
  cases HK with
  | projection HE HP RO =>
    obtain ⟨later, j, major, k, hj, RJ, RK⟩ := pi_inert_observer_ancestry_readout
      heq hs hi hp hf hz HLeast hout HT R (.projection HE HP RO) (by omega) HS HD RF
    exact ⟨later, j, major, k, by omega, RJ, RK⟩

/-- Typed replay preserves an actual application witness, as well as the
competitor's exact cost and original frame count. This prevents minimum
selection from losing the application rank used by terminal progress. -/
theorem PiInertProjectionApplicationRun.replay_competitor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames)
    (HE : ErasedTypedEquality Δ e candidate) (HK : K candidate cost) :
    PiInertProjectionApplicationRun D Ω family index out Δ K candidate cost frames := by
  induction H generalizing candidate cost with
  | application HT W HTnext R H =>
    obtain ⟨n, cs, endpoint, tailCost, rfl, RC, HK⟩ := HK
    have EQ := (HE.subst W.interpretation).mkApps HTnext
    have EO := ErasedTypedEquality.pi_inert_compute heq hs HTnext R.forget
    have EC := ErasedTypedEquality.pi_inert_compute heq hs EQ.target RC.forget
    exact .application HE.target W EQ.target RC
      (H.replay_competitor heq hs (EO.symm.trans (EQ.trans EC)) HK)
  | retained HT SD RD WI H ih =>
    have EQ := HE.subst WI
    simp only [ProofShape.subst_id] at EQ
    have HL := EQ.lamBody (typed_spine_head H.forget.forget.typed)
    exact .retained HE.target SD RD WI (ih (HL.mkApps H.forget.forget.typed) HK)

/-- Replaying any raw competitor from the original typed source retains the
selected application witness, even when every intermediate endpoint changes. -/
theorem PiInertProjectionApplicationRun.replay_from_source
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    PiInertProjectionApplicationRun D Ω family index out Δ K candidate cost frames := by
  exact H.replay_competitor heq hs
    ((ErasedTypedEquality.pi_inert_compute heq hs HT R.forget).symm.trans
      (ErasedTypedEquality.pi_inert_compute heq hs HT RC.forget)) HK

/-- Minimize over all raw source-path/continuation competitors while retaining
the exact original K, frame count AND application witness. No restriction is
added to the competitors. The minimum is bounded by any supplied competitor. -/
theorem PiInertProjectionApplicationRun.minimize_competitor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    ∃ smaller, smaller ≤ j+cost ∧
      ∃ later a endpoint b,
        ScopedComputeCount (PiInertStage D later) a Δ source endpoint ∧
        PiInertProjectionApplicationRun D Ω family index out Δ K endpoint b frames ∧
        a+b = smaller ∧
        ∀ stage c endpoint' d, ScopedComputeCount (PiInertStage D stage) c Δ source endpoint' →
          K endpoint' d → smaller ≤ c+d := by
  obtain ⟨smaller, hle, later, a, endpoint, b, RA, HA, hab, HM⟩ :=
    H.forget.minimize_competitor heq hs HT R RC HK
  exact ⟨smaller, hle, later, a, endpoint, b, RA,
    H.replay_from_source heq hs HT R RA HA.forget.holds, hab, HM⟩

/-- Package application-preserving minimization for the existing native-root
classification interface. The selected application rank is retained. -/
theorem PiInertProjectionApplicationRun.competitor_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    ∃ smaller, smaller ≤ j+cost ∧
      PiInertProjectionApplicationMinimum D Ω family index out Δ source smaller frames := by
  obtain ⟨smaller, hle, later, a, endpoint, b, RA, HA, hab, HM⟩ :=
    H.minimize_competitor heq hs HT R RC HK
  exact ⟨smaller, hle, K, later, a, b, endpoint, HT, RA, HA, hab, HM⟩

/-- Ordinary context interpretation preserves the projected ancestry needed
by an application-witness readout call. The source-major computation stays
before the map; only administrative deletion and ordinary terminal selection
are transported. The target computation and application witness are actual. -/
theorem pi_inert_substitution_application_ancestry_readout {field value : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : ContextSubstitution Δ Θ τ)
    (HTimage : TypedSource Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]))
    (RImage : ScopedComputeCount (PiInertStage D stage) cs Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]) endpoint)
    (HK : PiInertProjectionApplicationRun D Ω family 0 out Θ K endpoint ck frames)
    (IH : PiInertPairAncestryApplicationReadout D Ω family info out (cs+ck) frames)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ before cm later j major k, cm+j+k ≤ fieldCost+cs+ck ∧
      ScopedComputeCount (PiInertStage D fieldStage) cm Δ source before ∧
      ScopedComputeCount (PiInertStage D later) j Θ (before.subst τ) major ∧ K major k := by
  obtain ⟨major, terminal, cm, HDterminal, RM, HF⟩ :=
    pi_inert_sorted_projection_terminal_frames_count heq hs HSort RF
  have HDimage := ((HD.trans HDterminal).subst τ)
  have HSortMajor := HSort.compute
    (ErasedScopedPrimitiveCertificateDescent.descent
      (pi_inert_stage_certificate_descent heq hs fieldStage)) RM.proj.forget
  have HSortImage : ControlTyping Θ (.proj family 0 (major.subst τ)) (.sort u) := by
    simpa only [ProofShape.subst] using HSortMajor.subst W
  have finish (terminalCost : Nat) (hcost : cm+terminalCost ≤ fieldCost)
      (RTerminal : ScopedComputeCount (PiInertStage D stage) terminalCost Θ
        (.proj family 0 (major.subst τ)) (terminal.subst τ)) :
      ∃ before cm later j major k, cm+j+k ≤ fieldCost+cs+ck ∧
        ScopedComputeCount (PiInertStage D fieldStage) cm Δ source before ∧
        ScopedComputeCount (PiInertStage D later) j Θ (before.subst τ) major ∧ K major k := by
    obtain ⟨later, j, endpoint, k, hj, RJ, RK⟩ :=
      IH HTimage RImage HK rfl HSortImage HDimage RTerminal
    exact ⟨major, cm, later, j, endpoint, k, by omega, RM, RJ, RK⟩
  rcases HF with ⟨ET, hc⟩ | ⟨RI, hc⟩
  · apply finish 0 (by omega)
    simpa only [ET, ProofShape.subst] using
      (ScopedComputeCount.beta (Step := PiInertStage D stage) (Δ := Θ)
        (BetaRed.refl (e := .proj family 0 (major.subst τ))))
  · exact finish 1 hc (.base (pi_inert_stage_core (.inl (.inl (.inl RI.subst)))))

/-- An arbitrary exposed retained terminal reads its incoming field ancestry
using application-witness readout at no larger primitive cost and the SAME
single frame. The application witness strictly lowers the secondary rank
from 3 to 2. Its body computation may contain arbitrary native roots; neither
component-only coverage nor a global minimum is assumed. -/
theorem pi_inert_retained_terminal_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (WI : ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id)
    (HFull : TypedSource Ω (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args))
    (HProj : TypedSource Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)))
    (RO : ScopedComputeCount (PiInertStage D n) cost Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)) out)
    (IH : ∀ bodyCost, bodyCost ≤ cost → PiInertPairAncestryApplicationReadout D Ω family info out bodyCost 1)
    (HSort : ControlTyping (A :: Ω) (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost (A :: Ω)
      (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+cost ∧
      ScopedComputeCount (PiInertStage D later) j (A :: Ω) source major ∧
      PiInertProjectionContinuation D Ω family 0 out (ProofShape.mkApps (.lam A' major) args) k := by
  have HObserver := TypedSource.pair_first_projection_sort hi hu hp hshape HProj
  obtain ⟨selected, selectedField, cp, co, hselection, RP, RI, RT⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HObserver hout hproj RO
  have HNon : ∀ C b rest, selected ≠ ProofShape.mkApps (.lam C b) rest := by
    cases RI with
    | projIota =>
      intro C b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  rcases RP.pi_inert_lambda_spine_or_beta with ⟨C, b, rest, cf, ca, _, E, _, _⟩ |
    ⟨C, bodyEnd, x, rest, cf, ca, cs, hsplit, RL, RX, RS⟩
  · exact (HNon C b rest E).elim
  have HTlam := typed_spine_head HFull
  have HTbody : TypedSource (A' :: Ω) (ProofShape.mkApps (.const info.ctorName []) [field, value]) :=
    (ScopedHole.lamBody A' .hole).typed HTlam
  obtain ⟨v, cd, cb, bodyStage, _, hfun, RDomain, RBody⟩ := typed_lambda_readout heq hs HTlam RL
  have WX : ContextSubstitution (A' :: Ω) Ω (ProofShape.Subst.one x) :=
    typed_lambda_argument_map heq hs HFull RX
  have RBeta : ScopedComputeCount (PiInertStage D n) 0 Ω
      (ProofShape.mkApps (.lam C bodyEnd) (x :: rest))
      (ProofShape.mkApps (bodyEnd.inst x) rest) := by
    simpa only [ProofShape.mkApps, Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D n)
        (BetaRed.beta (A := C) (b := bodyEnd) (a := x))).mkApps (ScopedArgumentsCount.refl (args := rest))
  have HTnext := HFull.pi_inert_compute heq hs ((RL.mkApps RX).trans RBeta).forget
  have RObserve : ScopedComputeCount (PiInertStage D n) (1+co) Ω (.proj family 0 selected) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RT
  have HBody : PiInertProjectionApplicationRun D Ω family 0 out (A' :: Ω)
      (PiInertApplicationContinuation D Ω (ProofShape.Subst.one x) rest
        (PiInertProjectionContinuation D Ω family 0 out)) bodyEnd (cs+(1+co)) 1 :=
    .application (HTbody.pi_inert_compute heq hs RBody.forget) (.inst WX)
      (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
      (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS)
      (.projection (HFull.pi_inert_compute heq hs RP.forget)
        (HProj.pi_inert_compute heq hs RP.proj.forget) RObserve)
  obtain ⟨before, cm, later, j, major, k, hcost, RM, RJ, RK⟩ :=
    pi_inert_substitution_application_ancestry_readout (field := field) (value := value) heq hs WI
      (by simpa only [ProofShape.subst_id] using HTbody)
      (by simpa only [ProofShape.subst_id] using RBody) HBody
      (IH (cb+(cs+(1+co))) (by omega)) HSort HD RF
  have RJ' : ScopedComputeCount (PiInertStage D later) j (A' :: Ω) before major := by
    simpa only [ProofShape.subst_id] using RJ
  exact ⟨fieldStage, cm, before, cd+j+ca+k, by omega, RM,
    rebuild_terminal_body RDomain RX RJ' RK⟩

/-- Initial component computation before a retained terminal is included in
the same application-rank progress. Its first-field cost is absorbed into
ancestry in the ORIGINAL annotation context before the terminal is read. -/
theorem pi_inert_components_retained_terminal_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HT : TypedSource (A :: Ω) (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RA : ScopedArgumentsCount (PiInertStage D componentStage) (A :: Ω) ca
      [field, value] [nextField, nextValue])
    (WI : ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id)
    (HFull : TypedSource Ω (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) args))
    (HProj : TypedSource Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) args)))
    (RO : ScopedComputeCount (PiInertStage D n) cost Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) args)) out)
    (IH : ∀ bodyCost, bodyCost ≤ cost → PiInertPairAncestryApplicationReadout D Ω family info out bodyCost 1)
    (HSort : ControlTyping (A :: Ω) (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost (A :: Ω)
      (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ca+cost ∧
      ScopedComputeCount (PiInertStage D later) j (A :: Ω) source major ∧
      PiInertProjectionContinuation D Ω family 0 out (ProofShape.mkApps (.lam A' major) args) k := by
  have HTfield : TypedSource (A :: Ω) field :=
    (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) value).typed HT
  cases RA with
  | cons RField rest =>
    cases rest with
    | cons RValue last =>
      cases last
      obtain ⟨nextLower, cNext, hcNext, RNext, HDNext⟩ := HD.compute heq hs HTfield RField
      have RAncestry := (RF.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage componentStage))).trans
        (RNext.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage componentStage)))
      obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := pi_inert_retained_terminal_ancestry_readout
        heq hs hi hu hp hshape hout hproj WI HFull HProj RO IH HSort HDNext RAncestry
      exact ⟨later, j, major, k, by omega, RJ, RK⟩

/-- Every one-frame continuation after a component pair path has ancestry
readout under the lower application rank. The application branch closes at
zero frames using the least failed budget. The retained branch must be a
terminal and uses the consuming application witness proved above. This
classifies the actual one-frame execution, not a chosen supply certificate. -/
theorem pi_inert_components_one_frame_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RA : ScopedArgumentsCount (PiInertStage D componentStage) Δ ca
      [field, value] [nextField, nextValue])
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) ck 1)
    (hbudget : ca+ck < budget)
    (IH : ∀ bodyCost, bodyCost ≤ ca+ck → PiInertPairAncestryApplicationReadout D Ω family info out bodyCost 1)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ca+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k := by
  cases HK with
  | application _ W HNext RNext HRest =>
    obtain ⟨later, j, major, k, hc, RJ, RK⟩ := pi_inert_components_application_ancestry_readout
      heq hs hi hp hf hz HT RA W HNext RNext HRest
      (pi_inert_ancestry_readout_zero_frames heq hs hi hp hf hz HLeast hout (by omega)) HSort HD RF
    exact ⟨later, j, major, k, by omega, RJ, RK⟩
  | retained _ _ _ WI HRest =>
    cases HRest with
    | projection HFull HProj RO =>
      exact pi_inert_components_retained_terminal_ancestry_readout
        heq hs hi hu hp hshape hout hproj HT RA WI HFull HProj RO
        (fun bodyCost hc => IH bodyCost (by omega)) HSort HD RF

end Lean4Lean.VEnv.Strengthening
