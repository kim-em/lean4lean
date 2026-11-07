import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionApplicationWitness

/-! # Force an application inside a retained projection terminal

An exposed pair observation selects a constructor. The outermost retained
lambda must therefore be consumed. Refocus the remaining inner retained
prefix while keeping this application witness. The original body and its
ambient field are unchanged; only retained annotations may change.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Split off the last retained binder before the observer. The inner prefix
keeps the original binder context; the outer annotation change and argument
vector are explicit, and the plugging equation holds for every raw body. -/
theorem PiInertRetainedPrefixCount.outermost
    (HP : PiInertRetainedPrefixCount D Δ Ω plug depth) (hd : 0 < depth) :
    ∃ A u domainStage cd A' args innerPlug innerDepth,
      PiInertRetainedPrefixCount D Δ (A :: Ω) innerPlug innerDepth ∧
      DomainSort Ω A u ∧ ScopedComputeCount (PiInertStage D domainStage) cd Ω A A' ∧
      ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id ∧
      depth = innerDepth+1 ∧
      ∀ body, plug body = ProofShape.mkApps (.lam A' (innerPlug body)) args := by
  induction HP with
  | refl => omega
  | @retained Δ A u n cd A' Ω plug depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl => exact ⟨A, u, n, cd, A', args, id, 0, .refl, SD, RD, WI, rfl, fun _ => rfl⟩
    · obtain ⟨B, v, stage, c, B', outerArgs, innerPlug, innerDepth,
        HI, SB, RB, WB, hdepth, EP⟩ := ih (by omega)
      exact ⟨B, v, stage, c, B', outerArgs, _, innerDepth+1,
        .retained SD RD WI HI, SB, RB, WB, by omega, fun _ => EP _⟩

omit [Params] in
private theorem subst_id_liftN (depth : Nat) :
    ProofShape.Subst.id.liftN depth = ProofShape.Subst.id := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [ProofShape.Subst.liftN, ih]
    funext i
    cases i <;> simp [ProofShape.Subst.lift, ProofShape.Subst.id, ProofShape.liftN, liftVar, Nat.add_comm]

/-- A nonempty retained terminal for the pair's first projection refocuses to
an application-bearing minimum of the exact same body. The frame count equals
the original retained depth and primitive cost does not increase. The output
context has that same depth over the observer and is interpreted by identity.
The assertion is application occurrence, not a strict count saving by itself. -/
theorem PiInertRetainedPrefixCount.pair_terminal_application_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HP : PiInertRetainedPrefixCount D Δ Ω plug depth) (hd : 0 < depth)
    (HT : TypedSource Ω (plug e)) (HTproj : TypedSource Ω (.proj family 0 (plug e)))
    (RO : ScopedComputeCount (PiInertStage D n) cost Ω (.proj family 0 (plug e)) out)
    (HM : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω
      (.proj family 0 (plug e)) out → cost ≤ j) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Δ (telescope ++ Ω) ProofShape.Subst.id ∧ smaller ≤ cost ∧
      PiInertProjectionApplicationMinimum D Ω family 0 out (telescope ++ Ω) e smaller depth := by
  have HSort := TypedSource.pair_first_projection_sort hi hu hp hshape HTproj
  obtain ⟨selected, field, cp, ct, hc, RP, RI, RT⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HSort hout hproj RO
  have HTselected := HT.pi_inert_compute heq hs RP.forget
  have HPselected := HTproj.pi_inert_compute heq hs RP.proj.forget
  have RObserve : ScopedComputeCount (PiInertStage D n) (1+ct) Ω
      (.proj family 0 selected) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RT
  have HK : PiInertProjectionRunFrames D Ω family 0 out Ω
      (PiInertProjectionContinuation D Ω family 0 out) selected (1+ct) 0 :=
    .projection HTselected HPselected RObserve
  have HNon : ∀ A b args, selected ≠ ProofShape.mkApps (.lam A b) args := by
    cases RI with
    | projIota =>
      intro A b args E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  obtain ⟨A, u, domainStage, cd, A', args, innerPlug, innerDepth,
    HI, SD, RD, WI, hdepth, EP⟩ := HP.outermost hd
  rw [EP] at HT RP
  obtain ⟨smaller, hsmall, Hbody⟩ := pi_inert_lambda_spine_body_application_minimum
    heq hs HT RP HK (.inl HNon) (by
      rintro later j endpoint k RJ ⟨tailStage, RK⟩
      have RR := (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later tailStage))).proj.trans
        (RK.mono (pi_inert_stage_mono (Nat.le_max_right later tailStage)))
      have HB := HM _ _ (by simpa only [EP] using RR)
      omega)
  by_cases hz : innerDepth = 0
  · subst innerDepth
    cases HI with
    | refl =>
      refine ⟨[A'], smaller, by simp only [hdepth, List.length_cons, List.length_nil], ?_, by omega, ?_⟩
      · intro Γ hΓ EΓ
        exact WI hΓ EΓ
      · simpa only [hdepth, id_eq, List.cons_append, List.nil_append] using Hbody
  · have HB : PiInertProjectionApplicationMinimum D Ω family 0 out (A' :: Ω)
        (ProofShape.mkApps ((innerPlug e).subst ProofShape.Subst.id) []) smaller 1 := by
      simpa only [ProofShape.subst_id, ProofShape.mkApps] using Hbody
    obtain ⟨innerTelescope, last, hlen, WS, hlast, HLast⟩ :=
      HI.focus_application_nonempty heq hs (by omega) WI HB
    refine ⟨innerTelescope ++ [A'], last, ?_, ?_, by omega, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      omega
    · intro Γ hΓ EΓ
      simpa only [List.append_assoc, List.cons_append, List.nil_append, subst_id_liftN] using WS hΓ EΓ
    · simpa only [List.append_assoc, List.cons_append, List.nil_append, subst_id_liftN,
        ProofShape.subst_id, hdepth, Nat.add_comm] using HLast

/-- Every actual constructor-field endpoint either reaches the observer in
its own scope, has the strict application-frame decrease, or refocuses to an
application-bearing minimum at the identical endpoint. The last case retains
the original temporary depth and budget and cannot subsequently use the
pure-retained alternative when its selected body path is analyzed. Native eta
roots on that new body path still require their recursive readout invariant. -/
theorem PiInertProjectionRunFrames.pair_field_next_minimum {field : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K e ck frames)
    (hΔ : Δ = controls ++ Ω)
    (he : e = ProofShape.mkApps (.const ctor levels) (field.liftN controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cb+ck ≤ j+k)
    (hbudget : charge+cb+ck < budget) :
    (Δ = Ω ∧ PiInertProjectionContinuation D Ω family 0 out e ck) ∨
    (∃ nextControls σ nextFields smaller nextFrames,
      ContextSubstitution Δ (nextControls ++ Ω) σ ∧
      (field.liftN controls.length).subst σ = field.liftN nextControls.length ∧
      nextControls.length ≤ controls.length ∧ smaller ≤ ck ∧ charge+smaller < budget ∧
      nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (nextControls ++ Ω)
        (ProofShape.mkApps (.const ctor levels) (field.liftN nextControls.length :: nextFields))
        smaller nextFrames) ∨
    (∃ telescope smaller, telescope.length = controls.length ∧
      ContextSubstitution Δ (telescope ++ Ω) ProofShape.Subst.id ∧
      smaller ≤ ck ∧ charge+smaller < budget ∧
      PiInertProjectionApplicationMinimum D Ω family 0 out (telescope ++ Ω) e smaller frames) := by
  rcases HK.field_next_minimum heq hs hΔ he RP HM hbudget with
    ⟨plug, depth, observerStage, HP, HTplug, HTproj, RO, hf, EK⟩ | HNext
  · by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl => exact .inl ⟨rfl, observerStage, RO⟩
      | retained => omega
    · have HMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω
          (.proj family 0 (plug e)) out → ck ≤ j := by
        intro later j RJ
        have HB := HM n cb e j RP ((EK _ _).2 ⟨later, RJ⟩)
        omega
      obtain ⟨telescope, smaller, hlen, WS, hsmall, HApp⟩ :=
        HP.pair_terminal_application_minimum heq hs hi hu hp hshape hout hproj
          (by omega) HTplug HTproj RO HMin
      obtain ⟨originalTelescope, hlenOriginal, hctx⟩ := HP.contexts
      have hl := congrArg List.length (hΔ.symm.trans hctx)
      simp only [List.length_append, hlenOriginal] at hl
      exact .inr (.inr ⟨telescope, smaller, by omega, WS, hsmall, by omega,
        by simpa only [hf] using HApp⟩)
  · exact .inr (.inl HNext)

end Lean4Lean.VEnv.Strengthening
