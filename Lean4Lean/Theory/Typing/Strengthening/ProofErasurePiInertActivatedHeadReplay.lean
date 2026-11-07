import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConsumedConstructorCut

/-! # Replay an activated constructor head through retained wrappers

Only the independently scoped constructor history is renamed into the actual
application target. Ordinary equality recovers typing of the restored source,
including the final projection. The original guarded path is never substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_proj_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private tracked_spine tracked_compose
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedPrefixOrigin
open private identity_interpretation from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertHoleContinuation
open private retained_zero from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldProgress
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions} {field : ProofShape}

/-- Restore projection typing around an actual tracked-hole endpoint. The
ordinary major equality is reversed at its original type; no native guard
is transported backwards or through substitution. -/
theorem SpineBinderHole.pi_inert_projected_preimage {C : ScopedHole Ξ Δ}
    (HC : SpineBinderHole C) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (hf : f ≠ .proof)
    (RF : ScopedCompute (PiInertStage D n) Δ f short)
    (HNext : TypedSource Ξ (.proj family index (C.plug short))) :
    TypedSource Ξ (.proj family index (C.plug f)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HNext
  obtain ⟨major, rfl, hn, EM⟩ := erase_proj_inv Ee
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  obtain ⟨original, HE, EO⟩ := HC.pi_inert_preimage heq hs HT hf RF hΓ EΓ hm.hasType.2 EM
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HE.toU.of_l henv hΓ ht) T ht
  have hn' := mt (isProof_congr hΓ HP).2 hn
  exact ⟨Γ, .proj family index original, T, hΓ, EΓ, HP.hasType.2,
    by simp only [proofErase, if_neg hn', EO]⟩

/-- Projection typing also survives replay of an observer-scope constructor
history under the exact telescope of an actual application/binder hole. -/
theorem SpineBinderHole.pi_inert_lift_head_projected {C : ScopedHole Ξ Λ}
    (HC : SpineBinderHole C) (EΛ : Λ = controls ++ Ω)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Ω (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D n) cg Ω (.const ctor levels) short)
    (HNext : TypedSource Ξ (.proj family index
      (C.plug (ProofShape.mkApps (short.liftN controls.length) fields)))) :
    TypedSource Ξ (.proj family index (C.plug (ProofShape.mkApps (.const ctor levels) fields))) := by
  subst Λ
  have HU := C.typed ((ScopedHole.proj family index .hole).typed HNext)
  have RL : ScopedComputeCount (PiInertStage D n) cg (controls ++ Ω)
      (.const ctor levels) (short.liftN controls.length) := by
    simpa only [ProofShape.liftN] using pi_inert_lift_count_to_typed_context heq hs HU RF
  have HTctor : TypedSource (controls ++ Ω) (.const ctor levels) := by
    simpa only [ProofShape.subst] using HTlower.subst (TypedSource.telescope_renaming HU).interpretation
  obtain ⟨B, HB, EB⟩ := tracked_spine
    (.hole : SpineBinderHole (.hole : ScopedHole (controls ++ Ω) (controls ++ Ω))) fields
  obtain ⟨C', HC', EC⟩ := tracked_compose HC HB
  have E : ∀ e, C'.plug e = C.plug (ProofShape.mkApps e fields) := by
    intro e
    rw [EC, EB]
    rfl
  simpa only [E] using HC'.pi_inert_projected_preimage heq hs HTctor (by intro E; cases E) RL.forget
    (by simpa only [E] using HNext)

/-- Move the observer-scope head history into the actual target of any
retained prefix and endpoint map above that observer. Its exact count is
preserved. Both the whole application and any projection around it retain
typing at the restored constructor source. -/
theorem PiInertRetainedPrefixCount.observer_head_replay
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Ω (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D n) cg Ω (.const ctor levels) short)
    (HP : PiInertRetainedPrefixCount D (controls ++ Ω) Θ plug depth)
    (W : PiInertEndpointMap Θ Ξ τ) (hscope : Ω.length ≤ Ξ.length)
    (HTnext : TypedSource Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (short.liftN controls.length) fields)).subst τ) pending)) :
    TypedSource Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending) ∧
    ScopedComputeCount (PiInertStage D n) cg Ξ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (short.liftN controls.length) fields)).subst τ) pending) ∧
    (∀ family index, TypedSource Ξ (.proj family index (ProofShape.mkApps
        ((plug (ProofShape.mkApps (short.liftN controls.length) fields)).subst τ) pending)) →
      TypedSource Ξ (.proj family index (ProofShape.mkApps
        ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending))) := by
  have hΘscope : Ω.length ≤ Θ.length := by
    cases W with
    | identity => exact hscope
    | inst => simp only [List.length_cons]; omega
  obtain ⟨outer, EΘ, hd⟩ := HP.observer_suffix rfl hΘscope
  obtain ⟨rest, EΞ, hrest, EF⟩ := W.observer_tail EΘ hscope
  obtain ⟨telescope, hlen, C, HC, WS, EC⟩ := HP.application_hole W.interpretation pending
  have EH := EF short depth
  rw [hd] at EH
  have EImage : (short.liftN controls.length).subst (τ.liftN depth) =
      short.liftN (telescope ++ rest).length := by
    simpa only [List.length_append, hlen] using EH
  have EΛ : telescope ++ Ξ = (telescope ++ rest) ++ Ω := by
    simp only [EΞ, List.append_assoc]
  have HTnext' : TypedSource Ξ (C.plug (ProofShape.mkApps
      (short.liftN (telescope ++ rest).length) (fields.map (·.subst (τ.liftN depth))))) := by
    simpa only [EC, ProofShape.subst_mkApps, EImage] using HTnext
  obtain ⟨HTsource, RHead⟩ := HC.pi_inert_lift_head EΛ heq hs HTlower RF HTnext'
  have ESource : ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending =
      C.plug (ProofShape.mkApps (.const ctor levels) (fields.map (·.subst (τ.liftN depth)))) := by
    rw [EC, ProofShape.subst_mkApps]
    rfl
  refine ⟨by simpa only [ESource] using HTsource,
    by simpa only [ESource, EC, ProofShape.subst_mkApps, EImage] using RHead, ?_⟩
  intro family index HPnext
  have HH := HC.pi_inert_lift_head_projected EΛ heq hs HTlower RF
    (family := family) (index := index) (by simpa only [EC, ProofShape.subst_mkApps, EImage] using HPnext)
  simpa only [ESource] using HH

/-- An actual application after a retained computed constructor head
restores the full pair and strictly removes that application frame. The
lower head's exact charge is retained in the new minimum, and only the fixed
original prefix is used when comparing arbitrary competing paths. -/
theorem pi_inert_activated_head_application_progress
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HTlower : TypedSource Ω (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Ω (.const info.ctorName []) short)
    (HP : PiInertRetainedPrefixCount D (controls ++ Ω) Θ plug depth)
    (W : PiInertEndpointMap Θ Ξ τ)
    (HTplug : TypedSource Θ (plug (ProofShape.mkApps (short.liftN controls.length)
      [field.liftN controls.length, value])))
    (HTnext : TypedSource Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (short.liftN controls.length) [field.liftN controls.length, value])).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D suffixStage) cs Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (short.liftN controls.length) [field.liftN controls.length, value])).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Ξ K endpoint ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      PiInertApplicationContinuation D Ξ τ pending K (plug body) k → cb+cg+cs+ck ≤ j+k) :
    ∃ nextControls nextValue smaller, nextControls.length ≤ controls.length ∧ smaller ≤ cg+cs+ck ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue])
        smaller (frames+depth) := by
  have hscope : Ω.length ≤ Θ.length := by
    have hh := HK.forget.scope_length_le
    cases W with
    | identity => exact hh
    | inst => simp only [List.length_cons]; omega
  obtain ⟨HTplug', _, _⟩ := HP.observer_head_replay heq hs HTlower RF
    (.identity identity_interpretation) hscope (pending := []) (fields := [field.liftN controls.length, value])
    (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HTplug)
  have HTsource : TypedSource Θ (plug (ProofShape.mkApps (.const info.ctorName [])
      [field.liftN controls.length, value])) := by
    simpa only [ProofShape.subst_id, ProofShape.mkApps] using HTplug'
  obtain ⟨HTnext', RHead, _⟩ := HP.observer_head_replay heq hs HTlower RF W
    HK.forget.scope_length_le HTnext
  have RNext := (RHead.mono (pi_inert_stage_mono (Nat.le_max_left functionStage suffixStage))).trans
    (RT.mono (pi_inert_stage_mono (Nat.le_max_right functionStage suffixStage)))
  exact pi_inert_activated_pair_application_progress heq hs hi hp hf hz HP W HTsource HTnext' RNext HK RP
    (by intro later j body k RJ RK; have HH := HM later j body k RJ RK; omega)

/-- An application-bearing computed-head continuation gives a full pair
minimum with strictly fewer frames and at most its tail plus lower-head cost. -/
theorem PiInertProjectionApplicationRun.activated_head_next_minimum
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HTlower : TypedSource Ω (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Ω (.const info.ctorName []) short)
    (HK : PiInertProjectionApplicationRun D Ω family 0 out (controls ++ Ω) K
      (ProofShape.mkApps (short.liftN controls.length) [field.liftN controls.length, value]) ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      K body k → cb+cg+ck ≤ j+k) :
    ∃ nextControls nextValue smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ cg+ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue]) smaller nextFrames := by
  obtain ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
    HP, W, HTplug, HTnext, RT, HR, hc, hframes, EK⟩ := HK.next_application
  obtain ⟨nextControls, nextValue, smaller, hlen, hsmall, HNext⟩ :=
    pi_inert_activated_head_application_progress heq hs hi hp hf hz HTlower RF HP W HTplug HTnext RT HR RP
      (by
        intro later j body k RJ RK
        have HH := HM later j body k RJ ((EK body k).2 RK)
        omega)
  exact ⟨nextControls, nextValue, smaller, remaining+depth, hlen, by omega, by omega, HNext⟩

/-- A computed constructor head can be replayed at either the next actual
application or the purely retained terminal. The latter is refocused to an
application-bearing full pair at unchanged frame count, or reaches the
observer directly. Every result retains the same independently scoped field. -/
theorem PiInertProjectionRunFrames.activated_head_next_minimum
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HTlower : TypedSource Ω (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Ω (.const info.ctorName []) short)
    (HK : PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K
      (ProofShape.mkApps (short.liftN controls.length) [field.liftN controls.length, value]) ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      K body k → cb+cg+ck ≤ j+k) :
    (controls = [] ∧ ∃ stage, ScopedComputeCount (PiInertStage D stage) (cg+ck) Ω
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out) ∨
    (∃ nextControls nextValue smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ cg+ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue]) smaller nextFrames) ∨
    (∃ nextControls smaller, nextControls.length = controls.length ∧ smaller ≤ cg+ck ∧
      PiInertProjectionApplicationMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, value]) smaller frames) := by
  rcases HK.next_cut with
    ⟨plug, depth, observerStage, HP, HTplug, HTproj, RO, hframes, EK⟩ |
    ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hframes, EK⟩
  · obtain ⟨HTplug', RHead, HProject⟩ := HP.observer_head_replay heq hs HTlower RF
      (.identity identity_interpretation) (Nat.le_refl _) (pending := []) (fields := [field.liftN controls.length, value])
      (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HTplug)
    have HTsource : TypedSource Ω (plug (ProofShape.mkApps (.const info.ctorName [])
        [field.liftN controls.length, value])) := by
      simpa only [ProofShape.subst_id, ProofShape.mkApps] using HTplug'
    have HTproj' : TypedSource Ω (.proj family 0 (plug (ProofShape.mkApps (.const info.ctorName [])
        [field.liftN controls.length, value]))) := by
      simpa only [ProofShape.subst_id, ProofShape.mkApps] using HProject family 0
        (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HTproj)
    have RHead' : ScopedComputeCount (PiInertStage D functionStage) cg Ω
        (plug (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
        (plug (ProofShape.mkApps (short.liftN controls.length) [field.liftN controls.length, value])) := by
      simpa only [ProofShape.subst_id, ProofShape.mkApps] using RHead
    have RObserve := (RHead'.proj.mono (pi_inert_stage_mono (Nat.le_max_left functionStage observerStage))).trans
      (RO.mono (pi_inert_stage_mono (Nat.le_max_right functionStage observerStage)))
    by_cases hzero : depth = 0
    · obtain ⟨EΩ, EP⟩ := retained_zero (hzero ▸ HP)
      have hlen := congrArg List.length EΩ
      have EC : controls = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append] at hlen; omega)
      subst controls plug
      exact .inl ⟨rfl, max functionStage observerStage, by simpa only [id_eq, List.length_nil, ProofShape.liftN_zero] using RObserve⟩
    · have HMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω
          (.proj family 0 (plug (ProofShape.mkApps (.const info.ctorName [])
            [field.liftN controls.length, value]))) out → cg+ck ≤ j := by
        intro later j RJ
        have HH := HM n cb _ j RP ((EK _ _).2 ⟨later, RJ⟩)
        omega
      obtain ⟨telescope, smaller, hlen, WS, hsmall, HApp⟩ :=
        HP.pair_terminal_application_minimum heq hs hi hu hp hshape hout hproj
          (by omega) HTsource HTproj' RObserve HMin
      obtain ⟨originalTelescope, hlenOriginal, hctx⟩ := HP.contexts
      have hl := congrArg List.length hctx
      simp only [List.length_append, hlenOriginal] at hl
      have hlen' : telescope.length = controls.length := by omega
      exact .inr (.inr ⟨telescope, smaller, hlen', hsmall,
        by simpa only [hlen', hframes] using HApp⟩)
  · obtain ⟨nextControls, nextValue, smaller, hlen, hsmall, HNext⟩ :=
      pi_inert_activated_head_application_progress heq hs hi hp hf hz HTlower RF HP W HTplug HTnext RT HR RP
        (by
          intro later j body k RJ RK
          have HH := HM later j body k RJ ((EK body k).2 RK)
          omega)
    exact .inr (.inl ⟨nextControls, nextValue, smaller, remaining+depth, hlen, by omega, by omega, HNext⟩)

/-- An activated full-pair minimum whose selected native root is saturated
structure eta. Reading its projected first field across the continuation is
still open; this predicate assumes no readout or substitution stability. -/
def PiInertActivatedPairStructureMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out field : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) (application : Bool) : Prop :=
  ∃ stage pre pending target endpoint ct ck K,
    pre ++ pending = [field.liftN controls.length, value] ∧
    TypedSource (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ∧
    PiInertStage D stage (controls ++ Ω) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
    (pending = [] ∧ ∃ guardStage, guardStage < stage ∧
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) (controls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) pre) target) ∧
    ScopedComputeCount (PiInertStage D stage) ct (controls ++ Ω) (ProofShape.mkApps target pending) endpoint ∧
    PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K endpoint ck frames ∧ 1+ct+ck = cost ∧
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) tail →
      K tail k → cost ≤ j+k) ∧
    (application = true → PiInertProjectionApplicationRun D Ω family 0 out
      (controls ++ Ω) K endpoint ck frames)

/-- A retained activated function eta replays its independently lowered
head through the next application or retained terminal. The first-field
history is charged separately, and the frame/application rank strictly falls.
Only an actual structure root is returned as a native boundary. -/
theorem PiInertActivatedPairRetainedBoundaryMinimum.head_replay_progress
    (HFail : PiInertPairProjectionBudgetFailure D Ω family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HTfield : TypedSource Ω field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Ω original field)
    (H : PiInertActivatedPairRetainedBoundaryMinimum D Ω family info out field controls value cost frames application)
    (hbudget : charge+cost < budget) :
    PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application ∨
    (∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Ω short ∧ ScopedComputeCount (PiInertStage D later) charge' Ω original short ∧
      charge'+smaller < budget ∧ smaller ≤ cost ∧
      2*nextFrames + (if nextApplication then 0 else 1) < 2*frames + (if application then 0 else 1) ∧
      PiInertActivatedPairMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication) := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR, HNative, RT, HK, hc, HM, HApp⟩ := H
  rcases HNative with ⟨EP, HRetained, guardStage, hg, HE⟩ | HStructure
  · subst pre
    have E : pending = [field.liftN controls.length, value] := EArgs
    subst pending
    have HTlower : TypedSource Ω (.const info.ctorName []) := typed_spine_head HFail.1
    obtain ⟨head, C, body, fields, cg, ca, HThead, RHead, EHead, EO, RX, hsplit⟩ :=
      HRetained.lower_constructor_head heq hs HTlower HT HR
    obtain ⟨short, slot, cf, cv, hargs, HTshort, RShort, EFields⟩ :=
      pi_inert_activated_pair_component_descent heq hs HTfield HT RX
    have RAll := (RField.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage stage))).trans
      (RShort.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage stage)))
    have RArgs := (ScopedComputeCount.beta (Step := PiInertStage D stage)
      (BetaRed.refl (e := .const info.ctorName []))).mkApps RX
    rw [EFields] at RArgs EO
    rw [EO] at HK HApp
    cases application with
    | true =>
      obtain ⟨nextControls, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩ :=
        (HApp rfl).activated_head_next_minimum heq hs hi hp hf hz HTlower RHead RArgs
          (by intro later j tail k RJ RK; have HH := HM later j tail k RJ RK; omega)
      exact .inr ⟨short, nextControls, nextValue, _, charge+cf, smaller, nextFrames, false,
        HTshort, RAll, by omega, by omega, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, .of_frame HNext⟩
    | false =>
      rcases HK.activated_head_next_minimum heq hs hi hu hp hf hz hshape hout hproj HTlower RHead RArgs
        (by intro later j tail k RJ RK; have HH := HM later j tail k RJ RK; omega) with
        ⟨EC, later, RO⟩ | ⟨nextControls, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩ |
        ⟨nextControls, smaller, hlen, hsmall, HNext⟩
      · have HTpair := HT.pi_inert_compute heq hs RArgs.forget
        subst controls
        have HTpair' : TypedSource Ω (ProofShape.mkApps (.const info.ctorName []) [short, slot]) := by
          simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HTpair
        obtain ⟨last, j, hj, RJ⟩ := HLeast.readout_below HTpair' RO (by omega)
        have RFinal := (RAll.mono (pi_inert_stage_mono (Nat.le_max_left (max fieldStage stage) last))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right (max fieldStage stage) last)))
        exact (HFail.2.2 _ _ (by omega) RFinal).elim
      · exact .inr ⟨short, nextControls, nextValue, _, charge+cf, smaller, nextFrames, false,
          HTshort, RAll, by omega, by omega, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, .of_frame HNext⟩
      · exact .inr ⟨short, nextControls, slot, _, charge+cf, smaller, frames, true,
          HTshort, RAll, by omega, by omega, by simp, .of_application HNext⟩
  · exact .inl ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
      HStructure, RT, HK, hc, HM, HApp⟩

/-- All activated function-eta cases terminate by primitive cost followed
by frame/application rank. The only native outcome in either phase is now
structure eta. The same original field history and strict failure budget
persist; structure-target readout remains the unresolved part of this route. -/
theorem PiInertActivatedPairMinimum.function_eta_eliminate_all
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
      PiInertActivatedPairStructureMinimum D Ω family info out short nextControls slot smaller nextFrames nextApplication) ∨
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
          · rcases HLast.head_replay_progress HFail HLeast heq hs hi hu hp hf hz hshape hout hproj
              HTshort RShort hsmall with HStructure |
              ⟨last, nextControls, nextValue, lastStage, lastCharge, nextCost, nextFrames, nextApp,
                HTlast, RLast, hbudgetLast, hcostLast, hrankLast, HNext⟩
            · exact .inl ⟨short, controls, slot, later, charge', smaller, frames, application,
                HTshort, RShort, hsmall, HStructure⟩
            · by_cases hstrict : nextCost < cost
              · exact costIH nextCost hstrict HTlast RLast HNext hbudgetLast
              · have E : nextCost = cost := by omega
                subst nextCost
                exact rankIH _ (by omega) HTlast RLast HNext hbudgetLast rfl
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

/-- The actual global empty-prefix cut below a least pair failure reaches
structure eta after activation or before an intermediate supply. All repeated
function-eta, component, and retained-terminal transitions have been removed.
The two structure readouts, and hence the full strengthening goal, remain open. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_weighted_structure_boundary
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
      PiInertActivatedPairStructureMinimum D Δ family info out short nextControls slot smaller nextFrames nextApplication) ∨
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
    exact HActivated.function_eta_eliminate_all HFail HLeast heq hs hi hu hp hf hz hshape hD hout hproj HTx RField hsmall
  · refine .inr ⟨x, [], A, controls, nextValue, n, charge, smaller, nextFrames, HTx, RField, hsmall, ?_⟩
    simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HNext



end Lean4Lean.VEnv.Strengthening
