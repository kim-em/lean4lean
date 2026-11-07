import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedHeadCommutation

/-! # Constructor minima after a retained function crosses the next application

Move the supply-base function history through the actual retained prefix,
then focus the restored constructor minimum. The same pending fresh field is
preserved or supplied, and the continuation has strictly fewer frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private fresh_field_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldActivation
open private retained_zero
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions} {K : ProofShape → Nat → Prop}

/-- Move a reserved lower constructor history into the next actual application
suffix, across any finite retained prefix. Both outcomes restore the constructor
as the source of an unrestricted minimum. The function charge stays in that
minimum; the old prefix and argument charges remain outside it. The next
minimum has strictly fewer frames, preserving or activating the same field. -/
theorem PiInertFreshFieldRun.constructor_head_next_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Δ (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const ctor levels) short)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K e ck frames)
    (he : e = ProofShape.mkApps (short.liftN (controls.length+1)) (.bvar controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) source
      (ProofShape.mkApps (.const ctor levels) args))
    (RX : ScopedArgumentsCount (PiInertStage D n) (controls ++ A :: Δ) ca args
      (.bvar controls.length :: fields))
    (hcost : cp+ca+cg+ck ≤ cost)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source body → K body k → cost ≤ j+k) :
    (∃ telescope σ nextFields smaller nextFrames, telescope.length = controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (telescope ++ Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = x.liftN telescope.length ∧
      fields.length ≤ nextFields.length ∧ smaller ≤ cg+ck ∧ cp+ca+smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const ctor levels) (x.liftN telescope.length :: nextFields)) smaller nextFrames) ∨
    (∃ nextControls σ nextFields smaller nextFrames, nextControls.length ≤ controls.length ∧
      ContextSubstitution (controls ++ A :: Δ) (nextControls ++ A :: Δ) σ ∧
      (ProofShape.bvar controls.length).subst σ = .bvar nextControls.length ∧
      fields.length ≤ nextFields.length ∧ smaller ≤ cg+ck ∧ cp+ca+smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
        (ProofShape.mkApps (.const ctor levels) (.bvar nextControls.length :: nextFields)) smaller nextFrames) := by
  subst e
  rcases HK.next_application with
    ⟨plug, depth, m, cs, endpoint, ck', K', remaining, pending,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩ |
    ⟨beforeControls, nextControls, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HTnext, RT, HR, hc, hf, hd, EK⟩
  · apply Or.inl
    have HMin := pi_inert_commute_retained_head_supply heq hs HTlower RF RP RX HP hd W
      HTnext RT HR (by omega) (fun later j tail k RJ RK => HM later j tail k RJ ((EK tail k).2 RK))
    by_cases hz : depth = 0
    · subst depth
      have EC : controls = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst controls
      obtain ⟨_, EP⟩ := retained_zero HP
      subst plug
      refine ⟨[], ProofShape.Subst.one x, fields.map (·.subst (ProofShape.Subst.one x)) ++ pending,
        cg+cs+ck', remaining, rfl, W, ?_, by simp, by omega, by omega, by omega, ?_⟩
      · simp only [List.length_nil, ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.liftN_zero]
      · simpa only [id_eq, List.length_nil, List.nil_append, ProofShape.subst_mkApps,
          ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.liftN_zero,
          List.map_cons, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
        HP.focus_projection_nonempty heq hs (by omega) W HMin
      have EField := fresh_field_image (depth := depth) (x := x)
      change (ProofShape.Subst.one x).liftN depth depth = x.liftN depth at EField
      refine ⟨telescope, (ProofShape.Subst.one x).liftN depth,
        fields.map (·.subst ((ProofShape.Subst.one x).liftN depth)), smaller, remaining+depth,
        hlen.trans hd, WS, ?_, by simp, by omega, by omega, by omega, ?_⟩
      · simpa only [hlen, hd] using (fresh_field_image (depth := depth) (x := x))
      · simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
          ← hd, hlen, EField] using Hbody
  · apply Or.inr
    obtain ⟨hle, EF⟩ := W.fresh_field_transport
    have HMin := pi_inert_fresh_field_commute_retained_head_application heq hs HTlower RF RP RX HP hd W
      HTnext RT HR (by omega) (fun later j tail k RJ RK => HM later j tail k RJ ((EK tail k).2 RK))
    by_cases hz : depth = 0
    · subst depth
      obtain ⟨Ectx, EP⟩ := retained_zero HP
      have EC : controls = beforeControls := List.append_cancel_right Ectx
      subst beforeControls plug
      have EField := EF 0
      simp only [Nat.zero_add, ProofShape.Subst.liftN, ProofShape.subst] at EField
      refine ⟨nextControls, τ, fields.map (·.subst τ) ++ pending, cg+cs+ck', remaining,
        hle, W.interpretation, EField, by simp, by omega, by omega, by omega, ?_⟩
      simpa only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        EField, ← ProofShape.mkApps_append, List.cons_append] using HMin
    · obtain ⟨telescope, smaller, hlen, WS, hsmall, Hbody⟩ :=
        HP.focus_fresh_field_nonempty heq hs (by omega) W.interpretation HMin
      have EField := EF depth
      refine ⟨telescope ++ nextControls, τ.liftN depth, fields.map (·.subst (τ.liftN depth)),
        smaller, remaining+depth, ?_, WS, ?_, by simp, by omega, by omega, by omega, ?_⟩
      · simp only [List.length_append, hlen]
        omega
      · simpa only [List.length_append, hlen, hd] using EField
      · change τ.liftN depth (depth+beforeControls.length) = .bvar (depth+nextControls.length) at EField
        simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
          ← hd, EField, List.length_append, hlen] using Hbody

/-- An actual retained empty-prefix constructor eta progresses to a constructor
minimum after the next application, even through arbitrary retained wrappers.
The same fresh field is preserved or activated by its distinguished supply.
Primitive cost does not increase and frames strictly decrease. In contrast to
computed-head progress, no residual function-history premise is needed by the
new minimum: that history, including the eta charge, is part of its body path.
Recursive readout at subsequent constructor roots remains to be proved. -/
theorem pi_inert_fresh_field_empty_eta_constructor_progress
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
        args.length ≤ fields.length ∧ smaller ≤ cg+ck ∧ cp+ca+smaller ≤ cost ∧ nextFrames < frames ∧
        PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
          (ProofShape.mkApps (.const info.ctorName []) (x.liftN telescope.length :: fields))
          smaller nextFrames) ∨
       (∃ nextControls fields smaller nextFrames, nextControls.length ≤ controls.length ∧
        args.length ≤ fields.length ∧ smaller ≤ cg+ck ∧ cp+ca+smaller ≤ cost ∧ nextFrames < frames ∧
        PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
          (ProofShape.mkApps (.const info.ctorName []) (.bvar nextControls.length :: fields))
          smaller nextFrames)) := by
  obtain ⟨short, domain, body, rest, cg, ca, HTshort, RShort, EL, E,
    RArgs, hsplit, hbound, hsmall, HMin⟩ :=
    pi_inert_fresh_field_empty_eta_retained_descent heq hs hi hu hshape SD RN RN' SD'
      HTlower HT RP HR RT HK hcost HM
  have harglen := RArgs.forget.length_eq
  simp only [List.length_cons] at harglen
  rcases HK.constructor_head_next_minimum heq hs HTlower RShort E RP RArgs (by omega) HM with
    ⟨telescope, σ, fields, smaller, nextFrames, hlen, WS, EF, hfields, hnext, hbudget, hf, HNext⟩ |
    ⟨nextControls, σ, fields, smaller, nextFrames, hlen, WS, EF, hfields, hnext, hbudget, hf, HNext⟩
  · exact ⟨short, cg, ca, HTshort, RShort, hsplit,
      .inl ⟨telescope, fields, smaller, nextFrames, hlen, by omega, hnext, hbudget, hf, HNext⟩⟩
  · exact ⟨short, cg, ca, HTshort, RShort, hsplit,
      .inr ⟨nextControls, fields, smaller, nextFrames, hlen, by omega, hnext, hbudget, hf, HNext⟩⟩

private theorem typed_pair_tail
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) (field :: fields)))
    (hlen : 1 ≤ fields.length) : ∃ value, fields = [value] := by
  cases fields with
  | nil => simp at hlen
  | cons value pending =>
    have HTall : TypedSource Δ (ProofShape.mkApps
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) pending) := by
      simpa only [← ProofShape.mkApps_append, List.cons_append, List.nil_append] using HT
    have HPair : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) :=
      typed_spine_head HTall
    obtain ⟨Γ, pair, hΓ, EΓ, hpair, Epair⟩ := TypedSource.closed_constructor_realize hi hp hz
      (by simp [hf]) HPair
    have EP := TypedSource.closed_record_pending_nil hi hΓ EΓ hpair
      (by simpa only [Epair] using HTall)
    exact ⟨value, by rw [EP]⟩

/-- For a full two-field constructor, arbitrary retained wrappers followed by
the next application restore a full two-field constructor minimum. The first
field is exactly the same fresh variable or the lifted distinguished supply;
typing excludes all additional pending arguments. Primitive cost cannot
increase and the continuation frame count strictly decreases. This closes the
retained empty-prefix eta transition needed by a recursive pair readout, not
the remaining structure roots or the complete readout theorem. -/
theorem pi_inert_fresh_pair_empty_eta_constructor_progress
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage)
      (controls ++ A :: Δ) (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (controls ++ A :: Δ) A' v)
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (HT : TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) original
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]))
    (HR : PiInertStage D n (controls ++ A :: Δ) (.const info.ctorName [])
      (.lam A' (.app (.const info.ctorName []) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        [.bvar controls.length, value]) endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      original tail → K tail k → cost ≤ j+k) :
    (∃ telescope nextValue smaller nextFrames, telescope.length = controls.length ∧
      smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) [x.liftN telescope.length, nextValue]) smaller nextFrames) ∨
    (∃ nextControls nextValue smaller nextFrames, nextControls.length ≤ controls.length ∧
      smaller ≤ cost ∧ nextFrames < frames ∧
      PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
        (ProofShape.mkApps (.const info.ctorName []) [.bvar nextControls.length, nextValue]) smaller nextFrames) := by
  obtain ⟨short, cg, ca, HTshort, RShort, hsplit, HNext⟩ :=
    pi_inert_fresh_field_empty_eta_constructor_progress heq hs hi hu hshape SD RN RN' SD'
      HTlower HT RP HR RT HK hcost HM
  rcases HNext with
    ⟨telescope, fields, smaller, nextFrames, hlen, hfields, hnext, hbudget, hframes, HMin⟩ |
    ⟨nextControls, fields, smaller, nextFrames, hlen, hfields, hnext, hbudget, hframes, HMin⟩
  · have HTpair : TypedSource (telescope ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) (x.liftN telescope.length :: fields)) := by
      obtain ⟨_, _, _, _, _, HTpair, _⟩ := HMin
      exact HTpair
    obtain ⟨nextValue, rfl⟩ := typed_pair_tail hi hp hf hz HTpair hfields
    exact .inl ⟨telescope, nextValue, smaller, nextFrames, hlen, by omega, hframes, HMin⟩
  · have HTpair : TypedSource (nextControls ++ A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) (.bvar nextControls.length :: fields)) := by
      obtain ⟨_, _, _, _, _, HTpair, _⟩ := HMin
      exact HTpair
    obtain ⟨nextValue, rfl⟩ := typed_pair_tail hi hp hf hz HTpair hfields
    exact .inr ⟨nextControls, nextValue, smaller, nextFrames, hlen, by omega, hframes, HMin⟩

end Lean4Lean.VEnv.Strengthening
