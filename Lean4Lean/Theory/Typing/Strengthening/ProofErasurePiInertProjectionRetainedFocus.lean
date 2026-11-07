import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionFrameProgress

/-! # Execute retained prefixes before a projection observer

A projection may directly observe an applied lambda. Therefore a terminal
projection and a next application are kept as separate alternatives. In the
application alternative, focus the actual interpreted body without transporting
its preceding guarded path through the substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {plug : ProofShape → ProofShape} {K : ProofShape → Nat → Prop}

/-- The original inner context has exactly the retained depth above the outer
context. Annotation computations do not change this original suffix. -/
theorem PiInertRetainedPrefixCount.contexts
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) :
    ∃ telescope, telescope.length = depth ∧ Δ = telescope ++ Θ := by
  induction H with
  | refl => exact ⟨[], rfl, rfl⟩
  | retained SD RD WI HP ih =>
    obtain ⟨telescope, hlen, rfl⟩ := ih
    exact ⟨_ :: telescope, by simp only [List.length_cons, hlen], rfl⟩

/-- Locate the exact next application, or the terminal projection after only
retained frames. Both alternatives preserve the predicate on all raw
competitors. No syntactic assumption rules out an applied lambda major. -/
theorem PiInertProjectionRunFrames.next_cut
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames) :
    (∃ plug depth n, PiInertRetainedPrefixCount D Δ Ω plug depth ∧
      TypedSource Ω (plug e) ∧ TypedSource Ω (.proj family index (plug e)) ∧
      ScopedComputeCount (PiInertStage D n) ck Ω (.proj family index (plug e)) out ∧
      frames = depth ∧
      ∀ body k, K body k ↔ PiInertProjectionContinuation D Ω family index out (plug body) k) ∨
    (∃ Θ Ξ τ pending plug depth n cs endpoint ck' K' remaining,
      PiInertRetainedPrefixCount D Δ Θ plug depth ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ (ProofShape.mkApps ((plug e).subst τ) pending) endpoint ∧
      PiInertProjectionRunFrames D Ω family index out Ξ K' endpoint ck' remaining ∧
      ck = cs+ck' ∧ frames = remaining+depth+1 ∧
      ∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k) := by
  induction H with
  | projection HT HP R =>
    exact .inl ⟨id, 0, _, .refl, HT, HP, R, rfl, fun _ _ => Iff.rfl⟩
  | application HT W HTnext R HK _ =>
    exact .inr ⟨_, _, _, _, id, 0, _, _, _, _, _, _, .refl, W, HT, HTnext, R, HK,
      rfl, by omega, fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    rcases ih with ⟨plug, depth, n, HP, HTplug, HTproj, R, hf, EK⟩ |
      ⟨Θ, Ξ, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
        HP, W, HTplug, HTnext, R, HR, hc, hf, EK⟩
    · exact .inl ⟨_, depth+1, n, .retained SD RD WI HP, HTplug, HTproj, R,
        by omega, fun _ _ => EK _ _⟩
    · exact .inr ⟨Θ, Ξ, τ, pending, _, depth+1, n, cs, endpoint, ck', K', remaining,
        .retained SD RD WI HP, W, HTplug, HTnext, R, HR, hc, by omega,
        fun _ _ => EK _ _⟩

/-- Execute a nonempty retained telescope in the target of its actual ordinary
substitution. The result keeps the exact lifted map and the target context's
unchanged suffix. Precisely one frame per retained binder is rebuilt above
the selected tail; primitive cost does not increase. The old guarded body
path is never transported through this substitution. -/
theorem PiInertRetainedPrefixCount.focus_projection_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) (hd : 0 < depth)
    (W : ContextSubstitution Θ Ξ τ)
    (HM : PiInertProjectionFrameMinimum D Ω family index out Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) cost frames) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧ smaller ≤ cost ∧
      PiInertProjectionFrameMinimum D Ω family index out (telescope ++ Ξ)
        (e.subst (τ.liftN depth)) smaller (frames+depth) := by
  induction H generalizing e Ξ τ pending cost frames with
  | refl => omega
  | @retained Δ A u n cd A' Θ plug depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        refine ⟨[A'.subst τ], smaller, rfl, ?_, hsmall, HMbody⟩
        intro Γ hΓ EΓ
        simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
          List.cons_append, List.nil_append] using
          (ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') W) hΓ EΓ)
    · obtain ⟨telescope, smaller, hlen, WS, hsmall, HMinner⟩ := ih (by omega) W HM
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      refine ⟨A'.subst (τ.liftN depth) :: telescope, last,
        by simp only [List.length_cons, hlen], ?_, Nat.le_trans hlast hsmall, ?_⟩
      · intro Γ hΓ EΓ
        simpa only [ProofShape.Subst.id, ProofShape.subst, ProofShape.Subst.liftN,
          List.cons_append, List.nil_append] using
          (ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') WS) hΓ EΓ)
      · simpa only [Nat.add_assoc, ProofShape.Subst.liftN, List.cons_append] using HMbody

/-- Fixing the preceding body computation leaves a genuine minimum at the
actual next application source. The arbitrary candidate suffix is inserted
into the original continuation through its pointwise predicate equality. -/
theorem pi_inert_projection_application_frame_minimum
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HT : TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Ξ K' endpoint ck frames)
    (EK : ∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cb+(cs+ck) ≤ j+k) :
    PiInertProjectionFrameMinimum D Ω family index out Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) (cs+ck) frames := by
  refine ⟨K', m, cs, ck, endpoint, HT, RT, HK, rfl, ?_⟩
  intro later j tail k RJ HL
  have HB := HM n cb e (j+k) RP ((EK _ _).2 ⟨later, j, tail, k, rfl, RJ, HL⟩)
  omega

/-- Cross a nonempty retained telescope and its next actual application. The
new source is the interpreted endpoint, with the exact lifted map and target
suffix. Primitive cost does not increase, and the selected continuation has
strictly fewer frames. This is a real suffix decrease, before any unrelated
refocusing; no substituted replay of the old body computation is required. -/
theorem PiInertRetainedPrefixCount.projection_application_progress
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HP : PiInertRetainedPrefixCount D Δ Θ plug depth) (hd : 0 < depth)
    (W : PiInertEndpointMap Θ Ξ τ)
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HT : TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Ξ K' endpoint ck remaining)
    (EK : ∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cb+(cs+ck) ≤ j+k)
    (hf : frames = remaining+depth+1) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧
      smaller ≤ cs+ck ∧ remaining+depth < frames ∧
      PiInertProjectionFrameMinimum D Ω family index out (telescope ++ Ξ)
        (e.subst (τ.liftN depth)) smaller (remaining+depth) := by
  have Hnext := pi_inert_projection_application_frame_minimum RP HT RT HK EK HM
  obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
    HP.focus_projection_nonempty heq hs hd W.interpretation Hnext
  exact ⟨telescope, smaller, hlen, WS, hsmall, by omega, Hbody⟩

/-- An actual identity or consuming map above the observer leaves that
observer's context as a literal suffix. Consumption cannot remove an observer
binder, since the selected continuation never increases context length. All
terms from the observer context remain the same lifted terms at the new depth,
including after lifting the map beneath any retained telescope. -/
theorem PiInertEndpointMap.observer_tail
    (W : PiInertEndpointMap Θ Ξ τ) (hΘ : Θ = outer ++ Ω)
    (hscope : Ω.length ≤ Ξ.length) :
    ∃ rest, Ξ = rest ++ Ω ∧ rest.length ≤ outer.length ∧
      ∀ (field : ProofShape) depth, (field.liftN (depth+outer.length)).subst (τ.liftN depth) =
        field.liftN (depth+rest.length) := by
  cases W with
  | identity WI =>
    subst Θ
    refine ⟨outer, rfl, Nat.le_refl _, ?_⟩
    intro field depth
    rw [Nat.add_comm depth outer.length, ← ProofShape.liftN_add,
      ProofShape.liftN_subst_liftN, ProofShape.subst_id, ProofShape.liftN_add,
      Nat.add_comm outer.length depth]
  | @inst A Ξ x WI =>
    cases outer with
    | nil =>
      simp only [List.nil_append] at hΘ
      have hh := congrArg List.length hΘ
      simp only [List.length_cons] at hh
      omega
    | cons B rest =>
      simp only [List.cons_append] at hΘ
      obtain ⟨rfl, rfl⟩ := List.cons.inj hΘ
      refine ⟨rest, rfl, by simp, ?_⟩
      intro field depth
      simp only [List.length_cons]
      rw [Nat.add_comm depth (rest.length+1), ← ProofShape.liftN_add,
        ProofShape.liftN_subst_liftN, ← ProofShape.liftN_add (n := rest.length) (m := 1),
        ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
        ProofShape.liftN_add, Nat.add_comm rest.length depth]

/-- A retained telescope that ends above the observer removes only temporary
binders. Recover its remaining temporary context and exact depth equation. -/
theorem PiInertRetainedPrefixCount.observer_suffix
    (HP : PiInertRetainedPrefixCount D Δ Θ plug depth)
    (hΔ : Δ = controls ++ Ω) (hscope : Ω.length ≤ Θ.length) :
    ∃ outer, Θ = outer ++ Ω ∧ depth+outer.length = controls.length := by
  obtain ⟨telescope, hlen, hctx⟩ := HP.contexts
  have hl := congrArg List.length (hΔ.symm.trans hctx)
  simp only [List.length_append, hlen] at hl
  have hd : depth ≤ controls.length := by omega
  have HE : (controls ++ Ω).drop depth = Θ := by
    rw [← hΔ, hctx, ← hlen, List.drop_append_length]
  refine ⟨controls.drop depth, ?_, ?_⟩
  · simpa only [List.drop_append_of_le_length hd] using HE.symm
  · simp only [List.length_drop]
    omega

/-- From an actual minimum ending at a constructor with an ambient first
field, either only retained frames remain before the projection, or the next
application yields a minimum with fewer frames and the same ambient field.
This includes the empty retained prefix: its pending arguments append after
the preserved first field. Primitive cost and the old field charge never
increase. The residual terminal alternative is explicit, not excluded by
assuming a constructor-shaped projection major. -/
theorem PiInertProjectionRunFrames.field_next_minimum {field : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames)
    (hΔ : Δ = controls ++ Ω)
    (he : e = ProofShape.mkApps (.const ctor levels) (field.liftN controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cb+ck ≤ j+k)
    (hbudget : charge+cb+ck < budget) :
    (∃ plug depth n, PiInertRetainedPrefixCount D Δ Ω plug depth ∧
      TypedSource Ω (plug e) ∧ TypedSource Ω (.proj family index (plug e)) ∧
      ScopedComputeCount (PiInertStage D n) ck Ω (.proj family index (plug e)) out ∧
      frames = depth ∧
      ∀ body k, K body k ↔ PiInertProjectionContinuation D Ω family index out (plug body) k) ∨
    (∃ nextControls σ nextFields smaller nextFrames,
      ContextSubstitution Δ (nextControls ++ Ω) σ ∧
      (field.liftN controls.length).subst σ = field.liftN nextControls.length ∧
      nextControls.length ≤ controls.length ∧ smaller ≤ ck ∧ charge+smaller < budget ∧
      nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family index out (nextControls ++ Ω)
        (ProofShape.mkApps (.const ctor levels) (field.liftN nextControls.length :: nextFields))
        smaller nextFrames) := by
  rcases HK.next_cut with HTerm |
    ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, EK⟩
  · exact .inl HTerm
  apply Or.inr
  have hscope : Ω.length ≤ Θ.length := by
    have hh := HR.forget.scope_length_le
    cases W with
    | identity => exact hh
    | inst => simp only [List.length_cons]; omega
  obtain ⟨outer, hΘ, hdepth⟩ := HP.observer_suffix hΔ hscope
  have HMin := pi_inert_projection_application_frame_minimum RP HTnext RT HR EK
    (by simpa only [hc] using HM)
  obtain ⟨rest, hΞ, hrest, EF⟩ := W.observer_tail hΘ HR.forget.scope_length_le
  by_cases hz : depth = 0
  · subst depth
    cases HP with
    | refl =>
      have hlen : outer.length = controls.length := by omega
      subst e Ξ
      refine ⟨rest, τ, fields.map (·.subst τ) ++ pending, cs+ck', remaining,
        W.interpretation, ?_, by omega, by omega, by omega, by omega, ?_⟩
      · simpa only [Nat.zero_add, ProofShape.Subst.liftN, hlen] using EF field 0
      · have HE := EF field 0
        simp only [Nat.zero_add, ProofShape.Subst.liftN, hlen] at HE
        simpa only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
          HE, ← ProofShape.mkApps_append, List.cons_append] using HMin
  · have he' : e = ProofShape.mkApps (.const ctor levels)
        (field.liftN (depth+outer.length) :: fields) := by simpa only [hdepth] using he
    obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
      HP.focus_projection_nonempty heq hs (by omega) W.interpretation HMin
    subst Ξ
    refine ⟨telescope ++ rest, τ.liftN depth, fields.map (·.subst (τ.liftN depth)),
      smaller, remaining+depth, ?_, ?_, ?_, by omega, by omega, by omega, ?_⟩
    · intro Γ hΓ EΓ
      simpa only [List.append_assoc] using WS hΓ EΓ
    · simpa only [List.length_append, hlen, hdepth] using EF field depth
    · simp only [List.length_append, hlen]
      omega
    · rw [he'] at Hbody
      simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, EF] at Hbody
      simpa only [List.append_assoc, List.length_append, hlen] using Hbody

end Lean4Lean.VEnv.Strengthening
