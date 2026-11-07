import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionRetainedFocus

/-! # Preserve an actual application while focusing retained binders

A selected continuation with an application cannot fall back to the purely
retained terminal alternative. Lambda execution and retained-prefix focusing
preserve such a witness, without increasing primitive cost or adding more
frames than the exact retained depth.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map lambda_body_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

/-- An actual counted run whose retained prefix ends in an application.
The tail after that application is unrestricted, including a final projection. -/
inductive PiInertProjectionApplicationRun (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Nat → Prop where
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertProjectionRunFrames D Ω family index out Θ K e' ck frames →
      PiInertProjectionApplicationRun D Ω family index out Δ
        (PiInertApplicationContinuation D Θ τ args K) e (cs+ck) (frames+1)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertProjectionApplicationRun D Ω family index out Δ K
        (ProofShape.mkApps (.lam A' body) args) ck frames →
      PiInertProjectionApplicationRun D Ω family index out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck (frames+1)

/-- Forget application occurrence while retaining the exact frame count. -/
theorem PiInertProjectionApplicationRun.forget
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames) :
    PiInertProjectionRunFrames D Ω family index out Δ K e ck frames := by
  induction H with
  | application HT W HNext R HK => exact .application HT W HNext R HK
  | retained HT SD RD WI HK ih => exact .retained HT SD RD WI ih

/-- The selected application can be exposed without a terminal alternative.
Its actual substitution, suffix, predicate and frame equation are preserved. -/
theorem PiInertProjectionApplicationRun.next_application
    (H : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames) :
    ∃ Θ Ξ τ pending plug depth n cs endpoint ck' K' remaining,
      PiInertRetainedPrefixCount D Δ Θ plug depth ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ (ProofShape.mkApps ((plug e).subst τ) pending) endpoint ∧
      PiInertProjectionRunFrames D Ω family index out Ξ K' endpoint ck' remaining ∧
      ck = cs+ck' ∧ frames = remaining+depth+1 ∧
      ∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k := by
  induction H with
  | application HT W HNext R HK =>
    exact ⟨_, _, _, _, id, 0, _, _, _, _, _, _, .refl, W, HT, HNext, R, HK,
      rfl, by omega, fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    obtain ⟨Θ, Ξ, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
      HP, W, HTplug, HNext, R, HR, hc, hf, EK⟩ := ih
    exact ⟨Θ, Ξ, τ, pending, _, depth+1, n, cs, endpoint, ck', K', remaining,
      .retained SD RD WI HP, W, HTplug, HNext, R, HR, hc, by omega,
      fun _ _ => EK _ _⟩

/-- An unrestricted primitive-count minimum whose selected counted run
contains an actual application. No condition is added to competing endpoints. -/
def PiInertProjectionApplicationMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape)
    (Δ : List ProofShape) (source : ProofShape) (cost frames : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertProjectionApplicationRun D Ω family index out Δ K endpoint ck frames ∧ cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- Forget only the application witness, preserving all minimum data. -/
theorem PiInertProjectionApplicationMinimum.forget
    (H : PiInertProjectionApplicationMinimum D Ω family index out Δ source cost frames) :
    PiInertProjectionFrameMinimum D Ω family index out Δ source cost frames := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, R, HK.forget, hc, HM⟩

/-- Read any selected typed lambda-spine minimum in its original body scope,
using exactly one frame over the selected outer tail. A non-lambda endpoint
forces consumption; otherwise an application already in the selected suffix
survives either lambda branch. Competitors remain unrestricted. -/
theorem pi_inert_lambda_spine_body_application_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (R : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps (.lam A body) args) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K endpoint ck frames)
    (HA : (∀ A b args, endpoint ≠ ProofShape.mkApps (.lam A b) args) ∨
      PiInertProjectionApplicationRun D Ω family index out Δ K endpoint ck frames)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A body) args) tail → K tail k → ct+ck ≤ j+k) :
    ∃ smaller, smaller ≤ ct+ck ∧ PiInertProjectionApplicationMinimum D Ω family index out (A :: Δ) body smaller (frames+1) := by
  have HTlam : TypedSource Δ (.lam A body) := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody A .hole).typed HTlam
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, rfl, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have hexact := HM _ _ _ ck (lambda_body_replace RD RB RX) HK.forget.holds
    refine ⟨cb+ck, by omega, (fun body k => K (ProofShape.mkApps (.lam A' body) args') k),
      m, cb, ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · rcases HA with HNon | HApp
      · exact (HNon _ _ _ rfl).elim
      · exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
          (pi_inert_retained_frame_interpretation heq hs SD RD) HApp
    · intro later j tail k RJ HL
      have HB := HM _ _ _ k (lambda_body_replace RD RJ RX) HL
      omega
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have WI : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') := by
      intro Γ hΓ EΓ
      exact typed_lambda_argument_map heq hs HT RX hΓ EΓ
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam A' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
      simpa only [ProofShape.mkApps, Nat.zero_add] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
    have HTnext := HT.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
    have Ractual := ((lambda_body_replace RD RB RX).trans
      (Rbeta.mono (pi_inert_stage_mono (Nat.le_max_left n m)))).trans
      (RS.mono (pi_inert_stage_mono (Nat.le_max_left n m)))
    have hexact := HM _ _ _ ck Ractual HK.forget.holds
    refine ⟨cb+(cs+ck), by omega, PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HTbody, RB, ?_, rfl, ?_⟩
    · exact .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WI)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    · rintro later j tail k RJ ⟨suffixStage, tailCount, last, lastCost, hsum, RT, HL⟩
      have Rprefix := lambda_body_replace RD RJ RX
      have RBeta : ScopedComputeCount (PiInertStage D (max n later)) 0 Δ
          (ProofShape.mkApps (.lam A' tail) (x' :: xs')) (ProofShape.mkApps (tail.inst x') xs') := by
        simpa only [ProofShape.mkApps, Nat.zero_add] using
          (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
            (BetaRed.beta (A := A') (b := tail) (a := x'))).mkApps (ScopedArgumentsCount.refl (args := xs'))
      have RT' : ScopedComputeCount (PiInertStage D suffixStage) tailCount Δ
          (ProofShape.mkApps (tail.inst x') xs') last := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RT
      have RR := ((Rprefix.trans RBeta).mono
        (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
        (RT'.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
      have HB := HM _ _ _ lastCost RR HL
      omega

/-- Body readout preserves the actual application witness from the tail. -/
theorem PiInertProjectionApplicationMinimum.lambda_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertProjectionApplicationMinimum D Ω family index out Δ
      (ProofShape.mkApps (.lam A body) args) cost frames) :
    ∃ smaller, smaller ≤ cost ∧ PiInertProjectionApplicationMinimum D Ω family index out
      (A :: Δ) body smaller (frames+1) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨smaller, hsmall, Hbody⟩ := pi_inert_lambda_spine_body_application_minimum
    heq hs HT R HK.forget (.inr HK) (by simpa only [hc] using HM)
  exact ⟨smaller, by omega, Hbody⟩

/-- Execute a nonempty retained telescope in the target of its actual ordinary
substitution. The result keeps the exact lifted map and the target context's
unchanged suffix. Precisely one frame per retained binder is rebuilt above
the selected tail; primitive cost does not increase. The old guarded body
path is never transported through this substitution. The selected continuation
still contains an actual application. -/
theorem PiInertRetainedPrefixCount.focus_application_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) (hd : 0 < depth)
    (W : ContextSubstitution Θ Ξ τ)
    (HM : PiInertProjectionApplicationMinimum D Ω family index out Ξ
      (ProofShape.mkApps ((plug e).subst τ) pending) cost frames) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧ smaller ≤ cost ∧
      PiInertProjectionApplicationMinimum D Ω family index out (telescope ++ Ξ)
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

/-- With the application witness retained, the constructor-field endpoint
has a strict frame decrease with no terminal alternative. The original ambient
field and its budget survive identity or consuming substitutions, including
beneath every retained binder. -/
theorem PiInertProjectionApplicationRun.field_next_minimum {field : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HK : PiInertProjectionApplicationRun D Ω family index out Δ K e ck frames)
    (hΔ : Δ = controls ++ Ω)
    (he : e = ProofShape.mkApps (.const ctor levels) (field.liftN controls.length :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cb+ck ≤ j+k)
    (hbudget : charge+cb+ck < budget) :
    ∃ nextControls σ nextFields smaller nextFrames,
      ContextSubstitution Δ (nextControls ++ Ω) σ ∧
      (field.liftN controls.length).subst σ = field.liftN nextControls.length ∧
      nextControls.length ≤ controls.length ∧ smaller ≤ ck ∧ charge+smaller < budget ∧
      nextFrames < frames ∧
      PiInertProjectionFrameMinimum D Ω family index out (nextControls ++ Ω)
        (ProofShape.mkApps (.const ctor levels) (field.liftN nextControls.length :: nextFields))
        smaller nextFrames := by
  obtain ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, endpoint, ck', K', remaining,
    HP, W, HTplug, HTnext, RT, HR, hc, hf, EK⟩ := HK.next_application
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
