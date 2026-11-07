import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldFocus

/-! # Strict next-application progress for a tracked fresh field

Before the distinguished supply, actual application frames preserve the fresh
variable and its marked continuation. At supply, that variable becomes the
recorded argument below the retained telescope. Both cases remove one frame,
keep the exact interpreted field, and do not increase remaining primitive cost.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private fresh_field_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldActivation
variable [Params] {D : Definitions} {K : ProofShape → Nat → Prop}

private theorem retained_zero {plug : ProofShape → ProofShape}
    (H : PiInertRetainedPrefixCount D Ξ Θ plug 0) : Ξ = Θ ∧ plug = id := by
  cases H with
  | refl => exact ⟨rfl, rfl⟩

/-- Locate the actual next application after its retained prefix. It is either
the distinguished type-binder supply or an application strictly above it.
There is no purely retained terminal alternative, because the supplying
application is still recorded in the marked run. Both cases preserve the
predicate on every raw competitor and the exact remaining frame count. -/
theorem PiInertFreshFieldRun.next_application
    (H : PiInertFreshFieldRun D Δ family out A x controls K e ck frames) :
    (∃ plug depth n cs endpoint ck' K' remaining pending,
      PiInertRetainedPrefixCount D (controls ++ A :: Δ) (A :: Δ) plug depth ∧
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) ∧
      TypedSource (A :: Δ) (plug e) ∧
      TypedSource Δ (ProofShape.mkApps ((plug e).subst (ProofShape.Subst.one x)) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps ((plug e).subst (ProofShape.Subst.one x)) pending) endpoint ∧
      PiInertProjectionRunFrames D Δ family 0 out Δ K' endpoint ck' remaining ∧
      ck = cs+ck' ∧ frames = remaining+depth+1 ∧ depth = controls.length ∧
      ∀ body k, K body k ↔
        PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K' (plug body) k) ∨
    (∃ beforeControls nextControls τ pending plug depth n cs endpoint ck' K' remaining,
      PiInertRetainedPrefixCount D (controls ++ A :: Δ) (beforeControls ++ A :: Δ) plug depth ∧
      PiInertEndpointMap (beforeControls ++ A :: Δ) (nextControls ++ A :: Δ) τ ∧
      TypedSource (beforeControls ++ A :: Δ) (plug e) ∧
      TypedSource (nextControls ++ A :: Δ) (ProofShape.mkApps ((plug e).subst τ) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs (nextControls ++ A :: Δ)
        (ProofShape.mkApps ((plug e).subst τ) pending) endpoint ∧
      PiInertFreshFieldRun D Δ family out A x nextControls K' endpoint ck' remaining ∧
      ck = cs+ck' ∧ frames = remaining+depth+1 ∧ depth+beforeControls.length = controls.length ∧
      ∀ body k, K body k ↔
        PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ pending K' (plug body) k) := by
  induction H with
  | supply HT W HNext RNext HK =>
    exact .inl ⟨id, 0, _, _, _, _, _, _, _, .refl, W, HT, HNext, RNext, HK,
      rfl, by omega, rfl, fun _ _ => Iff.rfl⟩
  | application HT W HNext RNext HK _ =>
    exact .inr ⟨_, _, _, _, id, 0, _, _, _, _, _, _, .refl, W, HT, HNext, RNext, HK,
      rfl, by omega, by omega, fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    rcases ih with
      ⟨plug, depth, n, cs, endpoint, ck', K', remaining, pending,
        HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩ |
      ⟨beforeControls, nextControls, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
        HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩
    · exact .inl ⟨_, depth+1, n, cs, endpoint, ck', K', remaining, pending,
        .retained SD RD WI HP, W, HTplug, HTnext, RT, HR, hc, by omega,
        by simp only [List.length_cons]; omega, fun _ _ => EK _ _⟩
    · exact .inr ⟨beforeControls, nextControls, τ, pending, _, depth+1, n, cs, endpoint, ck', K', remaining,
        .retained SD RD WI HP, W, HTplug, HTnext, RT, HR, hc, by omega,
        by simp only [List.length_cons]; omega, fun _ _ => EK _ _⟩

/-- The fresh-field image under an application above the distinguished binder
remains the corresponding fresh variable beneath any retained depth. The
number of temporary binders cannot increase across that application. -/
theorem PiInertEndpointMap.fresh_field_transport
    (W : PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ) :
    nextControls.length ≤ controls.length ∧ ∀ depth,
      (ProofShape.bvar (depth+controls.length)).subst (τ.liftN depth) =
        .bvar (depth+nextControls.length) := by
  obtain ⟨rest, E, hrest, EF⟩ := W.observer_tail (Ω := A :: Δ) rfl (by simp)
  have hlen := congrArg List.length E
  simp only [List.length_append] at hlen
  have hh : rest.length = nextControls.length := by omega
  refine ⟨by omega, ?_⟩
  intro depth
  simpa only [ProofShape.liftN, liftVar, Nat.lt_irrefl, ↓reduceIte, Nat.add_zero, hh] using EF (.bvar 0) depth

/-- Advance a constructor endpoint with the tracked fresh type field through
its actual next application. Supply activates the recorded argument beneath
exactly the retained telescope. An earlier application preserves the fresh
variable and the SAME future supply. Both alternatives strictly reduce the
selected frame count and cost at most the old remaining continuation, including
zero-depth prefixes. No old guarded body path is substituted or replayed in
a new scope. Native roots on the new body path still require field readout. -/
theorem PiInertFreshFieldRun.field_next_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HK : PiInertFreshFieldRun D Δ family out A x controls K e ck frames)
    (he : e = ProofShape.mkApps (.const ctor levels) (.bvar controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ A :: Δ) source e)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source body → K body k → cb+ck ≤ j+k) :
    (∃ telescope σ nextFields smaller nextFrames, telescope.length = controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (telescope ++ Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = x.liftN telescope.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Δ family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const ctor levels) (x.liftN telescope.length :: nextFields)) smaller nextFrames) ∨
    (∃ nextControls σ nextFields smaller nextFrames, nextControls.length ≤ controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (nextControls ++ A :: Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = .bvar nextControls.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertFreshFieldMinimum D Δ family out A x nextControls
        (ProofShape.mkApps (.const ctor levels) (.bvar nextControls.length :: nextFields)) smaller nextFrames) := by
  rcases HK.next_application with
    ⟨plug, depth, m, cs, endpoint, ck', K', remaining, pending,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩ |
    ⟨beforeControls, nextControls, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩
  · apply Or.inl
    have HMin := pi_inert_projection_application_frame_minimum RP HTnext RT HR EK
      (by simpa only [hc] using HM)
    by_cases hz : depth = 0
    · subst depth
      have EC : controls = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst controls
      obtain ⟨_, EP⟩ := retained_zero HP
      subst plug
      subst e
      refine ⟨[], ProofShape.Subst.one x, fields.map (·.subst (ProofShape.Subst.one x)) ++ pending,
        cs+ck', remaining, rfl, W, ?_, by omega, by omega, ?_⟩
      · simp only [List.length_nil, ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.liftN_zero]
      · simpa only [id_eq, List.length_nil, List.nil_append, ProofShape.subst_mkApps,
          ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.liftN_zero,
          List.map_cons, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · have he' : e = ProofShape.mkApps (.const ctor levels) (.bvar depth :: fields) := by simpa only [hd] using he
      obtain ⟨telescope, smaller, hlen, WS, hsmall, _, Hbody⟩ :=
        HP.fresh_field_application_progress heq hs (by omega) W he' RP HTnext RT HR EK
          (by simpa only [hc] using HM)
      refine ⟨telescope, (ProofShape.Subst.one x).liftN depth,
        fields.map (·.subst ((ProofShape.Subst.one x).liftN depth)), smaller, remaining+depth,
        hlen.trans hd, WS, ?_, by omega, by omega, ?_⟩
      · simpa only [hlen, hd] using (fresh_field_image (depth := depth) (x := x))
      · simpa only [hlen] using Hbody
  · apply Or.inr
    obtain ⟨hle, EF⟩ := W.fresh_field_transport
    have HMin := pi_inert_fresh_field_application_minimum RP HTnext RT HR EK
      (by simpa only [hc] using HM)
    by_cases hz : depth = 0
    · subst depth
      obtain ⟨Ectx, EP⟩ := retained_zero HP
      have EC : controls = beforeControls := List.append_cancel_right Ectx
      subst beforeControls plug
      have EField := EF 0
      simp only [Nat.zero_add, ProofShape.Subst.liftN, ProofShape.subst] at EField
      subst e
      refine ⟨nextControls, τ, fields.map (·.subst τ) ++ pending, cs+ck', remaining,
        hle, W.interpretation, EField, by omega, by omega, ?_⟩
      simpa only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        EField, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · have he' : e = ProofShape.mkApps (.const ctor levels) (.bvar (depth+beforeControls.length) :: fields) := by
        simpa only [hd] using he
      obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
        HP.focus_fresh_field_nonempty heq hs (by omega) W.interpretation HMin
      have EField := EF depth
      refine ⟨telescope ++ nextControls, τ.liftN depth, fields.map (·.subst (τ.liftN depth)),
        smaller, remaining+depth, ?_, WS, ?_, by omega, by omega, ?_⟩
      · simp only [List.length_append, hlen]
        omega
      · simpa only [List.length_append, hlen, hd] using EField
      · rw [he'] at Hbody
        change τ.liftN depth (depth+beforeControls.length) = .bvar (depth+nextControls.length) at EField
        simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
          EField, List.length_append, hlen] using Hbody

/-- Analyze a marked constructor minimum without assuming its body retains
constructor components. The component case advances an actual application,
with no cost increase and strictly fewer frames, either activating `x` or
preserving the fresh field and the same future supply. Otherwise the selected
first non-level root is native function/structure eta, and its exact target
has a strictly smaller marked minimum. This gives the actual count/frame
progress needed for recursion; readout through the native targets remains open. -/
theorem PiInertFreshFieldMinimum.constructor_progress
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (H : PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: fields)) cost frames) :
    (∃ telescope nextFields smaller nextFrames, telescope.length = controls.length ∧
      smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Δ family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) (x.liftN telescope.length :: nextFields)) smaller nextFrames) ∨
    (∃ nextControls nextFields smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertFreshFieldMinimum D Δ family out A x nextControls
        (ProofShape.mkApps (.const info.ctorName []) (.bvar nextControls.length :: nextFields)) smaller nextFrames) ∨
    (∃ stage pre pending target cp ca smaller, ca ≤ cp ∧ cp+1+smaller ≤ cost ∧ smaller < cost ∧
      ScopedArgumentsCount (PiInertStage D stage) (controls ++ A :: Δ) ca
        (.bvar controls.length :: fields) (pre ++ pending) ∧
      ScopedComputeCount (PiInertStage D stage) cp (controls ++ A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: fields))
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) ∧
      PiInertStage D stage (controls ++ A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ConstructorEtaBodyRoot D stage (controls ++ A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      PiInertFreshFieldMinimum D Δ family out A x controls
        (ProofShape.mkApps target pending) smaller frames) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  rcases RB.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, values, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, pending, target, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    cases HA with
    | cons RFirst RRest =>
      have EF := RFirst.forget.pi_inert_bvar_fixed
      rcases HK.field_next_minimum heq hs (by rw [EF]) RB (by simpa only [hc] using HM) with
        ⟨telescope, σ, nextFields, smaller, nextFrames, hlen, WS, EField, hsmall, hf, HNext⟩ |
        ⟨nextControls, σ, nextFields, smaller, nextFrames, hlen, WS, EField, hsmall, hf, HNext⟩
      · exact .inl ⟨telescope, nextFields, smaller, nextFrames, hlen, by omega, hf, HNext⟩
      · exact .inr (.inl ⟨nextControls, nextFields, smaller, nextFrames, hlen, by omega, hf, HNext⟩)
  · cases HL
    have HSorted := HK.forget.forget.pair_sorted hi hu hp hshape
    have HRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi)
      hD HT RP HR HN RT HSorted hout hproj (cost := cost) (by omega) HM
    have RPrefixRoot : ScopedComputeCount (PiInertStage D n) (cp+1) (controls ++ A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: fields))
        (ProofShape.mkApps target pending) := by
      have RR := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))
      rw [← ProofShape.mkApps_append] at RR
      simpa only [Nat.add_zero] using RP.trans RR
    refine .inr (.inr ⟨n, pre, pending, target, cp, ca, ct+ck, hca, by omega, by omega,
      HA, RP, HR, HRoot, K, n, ct, ck, endpoint,
      HT.pi_inert_compute heq hs RPrefixRoot.forget, RT, HK, rfl, ?_⟩)
    intro later j tail k RJ RK
    have RAlt := (RPrefixRoot.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ tail k RAlt RK
    omega

end Lean4Lean.VEnv.Strengthening
