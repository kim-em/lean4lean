import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureReadoutInduction

/-! # Application progress for projected-field ancestry induction

The secondary frame count handles zero-cost applications. A saturated pair
cannot carry pending arguments at an actual typed endpoint map. Factor the
incoming projected ancestry before that map, transport only its ordinary
terminal selection, and recurse on the unrestricted target computation with
one fewer frame. Guarded computations stay in their original scopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The ancestry readout target restricted to an exact number of continuation
frames. Primitive cost is the primary induction parameter; frame count is the
secondary one for equal-cost application progress. Function-root and retained
frame progress remain open for the complete induction. -/
def PiInertPairAncestryReadoutFrames (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out : ProofShape) (cost frames : Nat) : Prop :=
  ∀ {Δ field value stage cb endpoint K ck},
    TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
    ScopedComputeCount (PiInertStage D stage) cb Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) endpoint →
    PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames →
    cb+ck = cost →
    ∀ {source u lower fieldStage fieldCost},
      ControlTyping Δ (.proj family 0 source) (.sort u) →
      AdministrativeHeadDeletion field lower →
      ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower →
      ∃ later j major k, j+k ≤ fieldCost+cost ∧
        ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k

/-- Unrestricted frame readout specializes to every exact frame count. -/
theorem PiInertPairAncestryReadout.frames {frames : Nat}
    (H : PiInertPairAncestryReadout D Ω family info out cost) :
    PiInertPairAncestryReadoutFrames D Ω family info out cost frames := by
  intro Δ field value stage cb endpoint K ck HT R HK hc source u lower fieldStage fieldCost HS HD RF
  exact H HT R HK hc HS HD RF

/-- Solving the secondary frame induction gives the existing cost-only
readout target, so smaller-cost structure-root calls may use any frame count. -/
theorem PiInertPairAncestryReadout.of_frames
    (H : ∀ frames, PiInertPairAncestryReadoutFrames D Ω family info out cost frames) :
    PiInertPairAncestryReadout D Ω family info out cost := by
  intro Δ field value stage cb endpoint K ck frames HT R HK hc source u lower fieldStage fieldCost HS HD RF
  exact H frames HT R HK hc HS HD RF

/-- Factor ancestry before an ordinary context map, then apply readout to
an arbitrary actual target pair execution. The result keeps the source-major
computation before the map and the target-major computation after it, with
one combined budget. Only ordinary terminal selection is substituted. -/
theorem pi_inert_substitution_ancestry_readout {field value : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : ContextSubstitution Δ Θ τ)
    (HTimage : TypedSource Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]))
    (RImage : ScopedComputeCount (PiInertStage D stage) cs Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Θ K endpoint ck frames)
    (IH : PiInertPairAncestryReadoutFrames D Ω family info out (cs+ck) frames)
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


/-- An application at a saturated pair has no pending arguments. Readout for
its target computation and tail at one fewer frame therefore supplies readout
for the whole application, at the SAME primitive cost. The actual target path
is arbitrary: it may contain native roots or end under retained binders. Only
the incoming ancestry's ordinary terminal selection crosses the context map. -/
theorem pi_inert_application_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (W : PiInertEndpointMap Δ Θ τ)
    (HTnext : TypedSource Θ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value]).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D stage) cs Θ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value]).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Θ K endpoint ck frames)
    (IH : PiInertPairAncestryReadoutFrames D Ω family info out (cs+ck) frames)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+cs+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧
      PiInertApplicationContinuation D Θ τ pending K major k := by
  have EP := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HT W.interpretation HTnext
  subst pending
  have HTimage : TypedSource Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil, ProofShape.mkApps] using HTnext
  have RImage : ScopedComputeCount (PiInertStage D stage) cs Θ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]) endpoint := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil, ProofShape.mkApps] using RT
  obtain ⟨before, cm, later, j, major, k, hc, RM, RJ, RK⟩ :=
    pi_inert_substitution_ancestry_readout heq hs W.interpretation HTimage RImage HK IH HSort HD RF
  exact ⟨fieldStage, cm, before, j+k, by omega, RM, later, j, major, k, rfl, RJ, RK⟩

/-- Component computation before an application is charged to the incoming
first-field ancestry. The target run needs readout only at its actual suffix
cost and one fewer frame; that is a lexicographically smaller induction call
even when BOTH the component prefix and the application cost zero. -/
theorem pi_inert_components_application_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RA : ScopedArgumentsCount (PiInertStage D componentStage) Δ ca [field, value] [nextField, nextValue])
    (W : PiInertEndpointMap Δ Θ τ)
    (HTnext : TypedSource Θ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D stage) cs Θ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Θ K endpoint ck frames)
    (IH : PiInertPairAncestryReadoutFrames D Ω family info out (cs+ck) frames)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ca+cs+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧
      PiInertApplicationContinuation D Θ τ pending K major k := by
  have RPair : ScopedComputeCount (PiInertStage D componentStage) ca Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
    simpa only [Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D componentStage) (Δ := Δ)
        (BetaRed.refl (e := .const info.ctorName []))).mkApps RA
  have HTpair := HT.pi_inert_compute heq hs RPair.forget
  have HTfield : TypedSource Δ field :=
    (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) value).typed HT
  cases RA with
  | cons RField rest =>
    cases rest with
    | cons RValue last =>
      cases last
      obtain ⟨nextLower, cNext, hcNext, RNext, HDNext⟩ := HD.compute heq hs HTfield RField
      have RAncestry := (RF.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage componentStage))).trans
        (RNext.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage componentStage)))
      obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := pi_inert_application_ancestry_readout
        heq hs hi hp hf hz HTpair W HTnext RT HK IH HSort HDNext RAncestry
      exact ⟨later, j, major, k, by omega, RJ, RK⟩

end Lean4Lean.VEnv.Strengthening
