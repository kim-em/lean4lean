import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshPairCutElimination
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedTerminalConsumption

/-! # Preserve a full activated pair at its next application

Only the first field is required to come from the observer scope. The value
may depend on the retained telescope. Actual application typing excludes
extra arguments, and focusing restores the exact two-field constructor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private retained_zero
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldProgress
variable [Params] {D : Definitions} {field : ProofShape}

/-- Advance an actual application after a retained full-pair endpoint. The
observer-scope field remains its literal lift, the second field is interpreted
by the actual map, and the restored source is again a full pair. The target
minimum has precisely the tail's frames plus retained depth; thus the selected
application contributes a strict frame decrease. -/
theorem pi_inert_activated_pair_application_progress
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HP : PiInertRetainedPrefixCount D (controls ++ Ω) Θ plug depth)
    (W : PiInertEndpointMap Θ Ξ τ)
    (HTplug : TypedSource Θ (plug (ProofShape.mkApps (.const info.ctorName [])
      [field.liftN controls.length, value])))
    (HTnext : TypedSource Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value])).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D suffixStage) cs Ξ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value])).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Ξ K endpoint ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      PiInertApplicationContinuation D Ξ τ pending K (plug body) k → cb+cs+ck ≤ j+k) :
    ∃ nextControls nextValue smaller, nextControls.length ≤ controls.length ∧ smaller ≤ cs+ck ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue])
        smaller (frames+depth) := by
  have hscope : Ω.length ≤ Θ.length := by
    have hh := HK.forget.scope_length_le
    cases W with
    | identity => exact hh
    | inst => simp only [List.length_cons]; omega
  obtain ⟨outer, hΘ, hdepth⟩ := HP.observer_suffix rfl hscope
  have HMin := pi_inert_projection_application_frame_minimum RP HTnext RT HK
    (fun _ _ => Iff.rfl) (by
      intro later j body k RJ RK
      have HH := HM later j body k RJ RK
      omega)
  obtain ⟨rest, hΞ, hrest, EF⟩ := W.observer_tail hΘ HK.forget.scope_length_le
  by_cases hzero : depth = 0
  · subst depth
    obtain ⟨EΘ, EP⟩ := retained_zero HP
    subst Θ plug
    have EP := TypedSource.closed_constructor_image_pending_nil hi hp hz
      (by simp [hf]) HTplug W.interpretation HTnext
    subst pending Ξ
    have hlen : outer.length = controls.length := by omega
    have HE := EF field 0
    simp only [Nat.zero_add, ProofShape.Subst.liftN, hlen] at HE
    refine ⟨rest, value.subst τ, cs+ck, by omega, Nat.le_refl _, ?_⟩
    simpa only [id_eq, ProofShape.mkApps, ProofShape.subst_mkApps, ProofShape.subst,
      List.map_cons, List.map_nil, HE, Nat.add_zero] using HMin
  · obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
      HP.focus_projection_nonempty heq hs (by omega) W.interpretation HMin
    subst Ξ
    have HE := EF field depth
    rw [hdepth] at HE
    refine ⟨telescope ++ rest, value.subst (τ.liftN depth), smaller, ?_, hsmall, ?_⟩
    · simp only [List.length_append, hlen]
      omega
    · simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil,
        HE, List.append_assoc, List.length_append, hlen] using Hbody

/-- An application-bearing continuation from a full activated pair removes
one frame, preserves the same lower field, and returns a full-pair minimum.
The second field need not have any independent lower-scope realization. -/
theorem PiInertProjectionApplicationRun.activated_pair_next_minimum
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HK : PiInertProjectionApplicationRun D Ω family 0 out (controls ++ Ω) K
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      K body k → cb+ck ≤ j+k) :
    ∃ nextControls nextValue smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue]) smaller nextFrames := by
  obtain ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
    HP, W, HTplug, HTnext, RT, HR, hc, hframes, EK⟩ := HK.next_application
  obtain ⟨nextControls, nextValue, smaller, hlen, hsmall, HNext⟩ :=
    pi_inert_activated_pair_application_progress heq hs hi hp hf hz HP W HTplug HTnext RT HR RP
      (by
        intro later j body k RJ RK
        have HH := HM later j body k RJ ((EK body k).2 RK)
        omega)
  exact ⟨nextControls, nextValue, smaller, remaining+depth, hlen, by omega, by omega, HNext⟩

/-- A full activated pair endpoint either reaches its observer directly,
advances an actual application with fewer frames, or exposes an application
inside its purely retained terminal. The last case preserves frame count but
adds an application witness, preventing another purely retained alternative.
All three outcomes keep the same independently scoped first field. -/
theorem PiInertProjectionRunFrames.activated_pair_next_minimum
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HK : PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) ck frames)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ Ω) source
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]))
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) source body →
      K body k → cb+ck ≤ j+k) :
    (controls = [] ∧ ∃ stage, ScopedComputeCount (PiInertStage D stage) ck Ω
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out) ∨
    (∃ nextControls nextValue smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, nextValue]) smaller nextFrames) ∨
    (∃ nextControls smaller, nextControls.length = controls.length ∧ smaller ≤ ck ∧
      PiInertProjectionApplicationMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN nextControls.length, value]) smaller frames) := by
  rcases HK.next_cut with
    ⟨plug, depth, observerStage, HP, HTplug, HTproj, RO, hframes, EK⟩ |
    ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hframes, EK⟩
  · by_cases hzero : depth = 0
    · obtain ⟨EΩ, EP⟩ := retained_zero (hzero ▸ HP)
      have hlen := congrArg List.length EΩ
      have EC : controls = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append] at hlen; omega)
      subst controls plug
      exact .inl ⟨rfl, observerStage, by simpa only [id_eq, List.length_nil, ProofShape.liftN_zero] using RO⟩
    · have HMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω
          (.proj family 0 (plug (ProofShape.mkApps (.const info.ctorName [])
            [field.liftN controls.length, value]))) out → ck ≤ j := by
        intro later j RJ
        have HH := HM n cb _ j RP ((EK _ _).2 ⟨later, RJ⟩)
        omega
      obtain ⟨telescope, smaller, hlen, WS, hsmall, HApp⟩ :=
        HP.pair_terminal_application_minimum heq hs hi hu hp hshape hout hproj
          (by omega) HTplug HTproj RO HMin
      obtain ⟨originalTelescope, hlenOriginal, hctx⟩ := HP.contexts
      have hl := congrArg List.length hctx
      simp only [List.length_append, hlenOriginal] at hl
      have hlen' : telescope.length = controls.length := by omega
      exact .inr (.inr ⟨telescope, smaller, hlen', hsmall,
        by simpa only [hlen', hframes] using HApp⟩)
  · obtain ⟨nextControls, nextValue, smaller, hlen, hsmall, HNext⟩ :=
      pi_inert_activated_pair_application_progress heq hs hi hp hf hz HP W HTplug HTnext RT HR RP
        (by
          intro later j body k RJ RK
          have HH := HM later j body k RJ ((EK body k).2 RK)
          omega)
    exact .inr (.inl ⟨nextControls, nextValue, smaller, remaining+depth, hlen, by omega, by omega, HNext⟩)

/-- Component computation of a full activated pair lowers just its first
field to the observer scope, preserving its exact stage and charge. The value
component stays in the upper context and contributes the remaining cost. -/
theorem pi_inert_activated_pair_component_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTfield : TypedSource Ω field)
    (HT : TypedSource (controls ++ Ω) source)
    (HA : ScopedArgumentsCount (PiInertStage D n) (controls ++ Ω) ca
      [field.liftN controls.length, value] fields) :
    ∃ short slot cf cv, ca = cf+cv ∧ TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D n) cf Ω field short ∧
      fields = [short.liftN controls.length, slot] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      obtain ⟨short, HTshort, RShort, EShort⟩ :=
        pi_inert_telescope_component_count_descend heq hs HTfield HT RF
      exact ⟨short, _, _, _, by simp only [Nat.add_zero]; rfl, HTshort, RShort, by rw [EShort]⟩

end Lean4Lean.VEnv.Strengthening
