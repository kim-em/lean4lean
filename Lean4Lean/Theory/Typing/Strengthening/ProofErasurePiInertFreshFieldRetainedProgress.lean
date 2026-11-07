import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldRetainedDescent

/-! # Advance a pending field below a function from the observer scope

A retained constructor-function endpoint descends to the observer scope.
Actual application frames preserve its literal lift while moving the tracked
fresh field, or activate that field at the distinguished supply. The original
function computation stays below and is not transported through substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private fresh_field_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldActivation
open private retained_zero
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldProgress
variable [Params] {D : Definitions} {K : ProofShape → Nat → Prop} {f : ProofShape}

omit [Params] in
private theorem supply_head_image :
    (f.liftN (depth+1)).subst ((ProofShape.Subst.one x).liftN depth) = f.liftN depth := by
  rw [Nat.add_comm depth 1, ← ProofShape.liftN_add, ProofShape.liftN_subst_liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- The exact observer-scope function remains the same lifted function across
an application above the distinguished binder, including under a retained
telescope. This is literal endpoint substitution, not guarded path transport. -/
theorem PiInertEndpointMap.pending_head_transport
    (W : PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ) :
    ∀ depth, (f.liftN (depth+controls.length+1)).subst (τ.liftN depth) =
      f.liftN (depth+nextControls.length+1) := by
  obtain ⟨rest, E, _, EF⟩ := W.observer_tail (Ω := Δ) (outer := controls ++ [A])
    (by simp only [List.append_assoc, List.cons_append, List.nil_append])
    (by simp only [List.length_append, List.length_cons]; omega)
  have hl := congrArg List.length E
  simp only [List.length_append, List.length_cons] at hl
  intro depth
  simpa only [List.length_append, List.length_cons, List.length_nil,
    show rest.length = nextControls.length+1 by omega, Nat.add_assoc] using EF f depth

/-- Advance the actual next application with a fresh field pending after any
function lifted from the observer scope. In particular, the function can be
the retained lambda returned by empty-prefix descent. Both alternatives keep
the exact same lower function and strictly fewer frames, with no cost increase;
the supply alternative activates x. Subsequent body computations remain actual
minima, and still require recursive field readout. -/
theorem PiInertFreshFieldRun.pending_field_next_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K e ck frames)
    (he : e = ProofShape.mkApps (f.liftN (controls.length+1)) (.bvar controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ A :: Δ) source e)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source body → K body k → cb+ck ≤ j+k) :
    (∃ telescope σ nextFields smaller nextFrames, telescope.length = controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (telescope ++ Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = x.liftN telescope.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (f.liftN telescope.length) (x.liftN telescope.length :: nextFields)) smaller nextFrames) ∨
    (∃ nextControls σ nextFields smaller nextFrames, nextControls.length ≤ controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (nextControls ++ A :: Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = .bvar nextControls.length ∧
      smaller ≤ ck ∧ nextFrames < frames ∧
      PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
        (ProofShape.mkApps (f.liftN (nextControls.length+1)) (.bvar nextControls.length :: nextFields)) smaller nextFrames) := by
  rcases HK.next_application with
    ⟨plug, depth, m, cs, endpoint, ck', K', remaining, pending,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩ |
    ⟨beforeControls, nextControls, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩
  · apply Or.inl
    have HHead := supply_head_image (f := f) (x := x) (depth := depth)
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
      · simpa only [id_eq, List.length_nil, List.nil_append, Nat.zero_add, ProofShape.subst_mkApps,
          ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.liftN_zero,
          ProofShape.lift_subst_cons, ProofShape.subst_id,
          List.map_cons, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · have he' : e = ProofShape.mkApps (f.liftN (depth+1)) (.bvar depth :: fields) := by simpa only [hd] using he
      obtain ⟨telescope, smaller, hlen, WS, hsmall, _, Hbody⟩ :=
        HP.projection_application_progress heq hs (by omega) (.inst W) RP HTnext RT HR EK
          (by simpa only [hc] using HM) rfl
      rw [he', ProofShape.subst_mkApps, HHead] at Hbody
      have EField := fresh_field_image (depth := depth) (x := x)
      change (ProofShape.Subst.one x).liftN depth depth = x.liftN depth at EField
      simp only [List.map_cons, ProofShape.subst, EField] at Hbody
      refine ⟨telescope, (ProofShape.Subst.one x).liftN depth,
        fields.map (·.subst ((ProofShape.Subst.one x).liftN depth)), smaller, remaining+depth,
        hlen.trans hd, WS, ?_, by omega, by omega, ?_⟩
      · simpa only [hlen, hd] using (fresh_field_image (depth := depth) (x := x))
      · simpa only [hlen] using Hbody
  · apply Or.inr
    obtain ⟨hle, EF⟩ := W.fresh_field_transport
    have EH := W.pending_head_transport (f := f)
    have HMin := pi_inert_fresh_field_application_minimum RP HTnext RT HR EK
      (by simpa only [hc] using HM)
    by_cases hz : depth = 0
    · subst depth
      obtain ⟨Ectx, EP⟩ := retained_zero HP
      have EC : controls = beforeControls := List.append_cancel_right Ectx
      subst beforeControls plug
      have EField := EF 0
      have EHead := EH 0
      simp only [Nat.zero_add, ProofShape.Subst.liftN] at EHead
      simp only [Nat.zero_add, ProofShape.Subst.liftN, ProofShape.subst] at EField
      subst e
      refine ⟨nextControls, τ, fields.map (·.subst τ) ++ pending, cs+ck', remaining,
        hle, W.interpretation, EField, by omega, by omega, ?_⟩
      simpa only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        EField, EHead, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · have he' : e = ProofShape.mkApps (f.liftN (depth+beforeControls.length+1)) (.bvar (depth+beforeControls.length) :: fields) := by
        simpa only [hd] using he
      obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
        HP.focus_fresh_field_nonempty heq hs (by omega) W.interpretation HMin
      have EField := EF depth
      refine ⟨telescope ++ nextControls, τ.liftN depth, fields.map (·.subst (τ.liftN depth)),
        smaller, remaining+depth, ?_, WS, ?_, by omega, by omega, ?_⟩
      · simp only [List.length_append, hlen]
        omega
      · simpa only [List.length_append, hlen, hd] using EField
      · rw [he', ProofShape.subst_mkApps, EH] at Hbody
        change τ.liftN depth (depth+beforeControls.length) = .bvar (depth+nextControls.length) at EField
        simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
          EField, List.length_append, hlen, Nat.add_assoc] using Hbody

/-- Execute a next application after the actual retained empty-prefix eta
cut. The counted function history is now in the observer scope and includes
the original eta charge. The same function persists literally through the
next application, while the fresh field is either preserved or activated.
Its reserved function/argument charges plus the new minimum stay within the
original budget, and frames strictly decrease. Further actual body paths at
these new minima still need recursive field readout. -/
theorem pi_inert_fresh_field_empty_eta_next_application
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage)
      (controls ++ A :: Δ) (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (controls ++ A :: Δ) A' v)
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (HT : TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) original
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (HR : PiInertStage D n (controls ++ A :: Δ) (.const info.ctorName [])
      (.lam A' (.app (.const info.ctorName []) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (.bvar controls.length :: args)) endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      original tail → K tail k → cost ≤ j+k) :
    ∃ short cg ca, TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) cg Δ (.const info.ctorName []) short ∧
      cg+ca = 1+ct ∧
      ((∃ telescope fields smaller nextFrames, telescope.length = controls.length ∧
        smaller ≤ ck ∧ cp+cg+ca+smaller ≤ cost ∧ nextFrames < frames ∧
        PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
          (ProofShape.mkApps (short.liftN telescope.length) (x.liftN telescope.length :: fields))
          smaller nextFrames) ∨
       (∃ nextControls fields smaller nextFrames, nextControls.length ≤ controls.length ∧
        smaller ≤ ck ∧ cp+cg+ca+smaller ≤ cost ∧ nextFrames < frames ∧
        PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
          (ProofShape.mkApps (short.liftN (nextControls.length+1)) (.bvar nextControls.length :: fields))
          smaller nextFrames)) := by
  obtain ⟨short, domain, body, rest, cg, ca, HTshort, RShort, EL, E,
    RArgs, hsplit, hbound, hsmall, HMin⟩ :=
    pi_inert_fresh_field_empty_eta_retained_descent heq hs hi hu hshape SD RN RN' SD'
      HTlower HT RP HR RT HK hcost HM
  have RWhole := (RP.trans ((ScopedComputeCount.base HR).mkApps
    (ScopedArgumentsCount.refl (args := .bvar controls.length :: args)))).trans RT
  rcases HK.pending_field_next_minimum heq hs E RWhole (by
    intro later j tail l RJ RK
    have HH := HM later j tail l RJ RK
    omega) with
    ⟨telescope, σ, fields, smaller, nextFrames, hlen, WS, EF, hnext, hf, HNext⟩ |
    ⟨nextControls, σ, fields, smaller, nextFrames, hlen, WS, EF, hnext, hf, HNext⟩
  · exact ⟨short, cg, ca, HTshort, RShort, hsplit,
      .inl ⟨telescope, fields, smaller, nextFrames, hlen, hnext, by omega, hf, HNext⟩⟩
  · exact ⟨short, cg, ca, HTshort, RShort, hsplit,
      .inr ⟨nextControls, fields, smaller, nextFrames, hlen, hnext, by omega, hf, HNext⟩⟩

end Lean4Lean.VEnv.Strengthening
