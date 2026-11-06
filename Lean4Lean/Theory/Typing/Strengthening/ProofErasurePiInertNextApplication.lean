import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedContinuation

/-! # Follow a typed continuation to its next actual application

A finite prefix of retained lambda frames is exposed syntactically. If the
current endpoint is not a carrier and the final output is, the selected
execution must encounter an application frame. Its original continuation
predicate is preserved pointwise, so the next scope inherits minimality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- The exact syntactic action of a finite prefix of retained lambda frames.
Annotations, arguments and ordinary binder interpretations are recorded;
there are no computation or substitution frames inside this prefix. -/
inductive PiInertRetainedPrefix (D : Definitions) :
    List ProofShape → List ProofShape → (ProofShape → ProofShape) → Prop where
  | refl : PiInertRetainedPrefix D Δ Δ id
  | retained : DomainSort Δ A u → ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertRetainedPrefix D Δ Θ plug →
      PiInertRetainedPrefix D (A :: Δ) Θ
        (fun e => plug (ProofShape.mkApps (.lam A' e) args))

/-- The first actual application after zero or more retained lambda frames.
Its identity or single-binder endpoint map, full typed source, chosen
computation, remaining typed execution and exact cost are retained. Pointwise equivalence describes the original continuation
on every competitor endpoint, not merely on its selected endpoint. -/
def PiInertNextApplication (D : Definitions) (Ω : List ProofShape) (out : ProofShape)
    (Δ : List ProofShape) (K : ProofShape → Nat → Prop) (e : ProofShape) (ck : Nat) : Prop :=
  ∃ Θ Ξ τ args plug n cs e' ck' K',
    PiInertRetainedPrefix D Δ Θ plug ∧ PiInertEndpointMap Θ Ξ τ ∧
    TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) args) ∧
    ScopedComputeCount (PiInertStage D n) cs Ξ (ProofShape.mkApps ((plug e).subst τ) args) e' ∧
    PiInertTypedContinuationRun D Ω out Ξ K' e' ck' ∧ cs+ck' = ck ∧
    ∀ endpoint k, K endpoint k ↔ PiInertApplicationContinuation D Ξ τ args K' (plug endpoint) k

/-- A non-exposed endpoint cannot reach an exposed final output through
retained lambda frames alone. Traverse the actual finite execution to its
next application, retaining all preceding annotations and the exact predicate
for competitors. This does not assume exposure of an intermediate endpoint. -/
theorem PiInertTypedContinuationRun.next_application
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck)
    (HE : CarrierExposure out) (hn : ¬ CarrierExposure e) :
    PiInertNextApplication D Ω out Δ K e ck := by
  induction H with
  | terminal => exact (hn HE).elim
  | application HT W HTnext R HK _ =>
    exact ⟨_, _, _, _, id, _, _, _, _, _, .refl, W, HT, HTnext, R, HK, rfl,
      fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    obtain ⟨Θ, Ξ, τ, args, plug, n, cs, e', ck', K', HP, W, HTplug, HTnext, R, HR, hc, EK⟩ :=
      ih (fun H => H.not_lambda_spine _ _ _ rfl)
    exact ⟨Θ, Ξ, τ, args, _, n, cs, e', ck', K', .retained SD RD WI HP,
      W, HTplug, HTnext, R, HR, hc, fun _ _ => EK _ _⟩

/-- Fixed-endpoint minimality for a continuation becomes a full computation
minimum in its next application scope. Competitors vary both the next path's
endpoint and its remaining continuation count at every finite stage. -/
theorem PiInertNextApplication.minimum
    (H : PiInertNextApplication D Ω out Δ K e ck)
    (hmin : ∀ k, K e k → ck ≤ k) :
    ∃ Θ Ξ τ args plug,
      PiInertRetainedPrefix D Δ Θ plug ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧
      PiInertTypedContinuationMinimum D Ω out Ξ
        (ProofShape.mkApps ((plug e).subst τ) args) ck := by
  obtain ⟨Θ, Ξ, τ, args, plug, n, cs, e', ck', K', HP, W, HTplug, HTnext, R, HR, hc, EK⟩ := H
  refine ⟨Θ, Ξ, τ, args, plug, HP, W, HTplug, K', n, cs, ck', e', HTnext, R, HR, hc, ?_⟩
  intro later j endpoint k RJ HK
  exact hmin (j+k) ((EK e (j+k)).2 ⟨later, j, endpoint, k, rfl, RJ, HK⟩)

/-- The same next application preserves joint minimality with a preceding
body path. In particular competitors may change the body endpoint and then
apply the exact retained-lambda prefix and endpoint substitution to it. No
old body computation is transported through the substitution. -/
theorem PiInertNextApplication.joint_minimum
    (H : PiInertNextApplication D Ω out Δ K e ck)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (hcost : cb+ck = cost)
    (hmin : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint →
      K endpoint k → cost ≤ j+k) :
    ∃ Θ Ξ τ args plug suffixStage cs e' ck' K',
      PiInertRetainedPrefix D Δ Θ plug ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) args) ∧
      ScopedComputeCount (PiInertStage D suffixStage) cs Ξ (ProofShape.mkApps ((plug e).subst τ) args) e' ∧
      PiInertTypedContinuationRun D Ω out Ξ K' e' ck' ∧ cb+cs+ck' = cost ∧
      PiInertTypedContinuationMinimum D Ω out Ξ (ProofShape.mkApps ((plug e).subst τ) args) ck ∧
      ∀ bodyStage tailStage j endpoint l tail k,
        ScopedComputeCount (PiInertStage D bodyStage) j Δ source endpoint →
        ScopedComputeCount (PiInertStage D tailStage) l Ξ
          (ProofShape.mkApps ((plug endpoint).subst τ) args) tail →
        K' tail k → cost ≤ j+l+k := by
  obtain ⟨Θ, Ξ, τ, args, plug, suffixStage, cs, e', ck', K', HP, W, HTplug, HTnext, RS, HR, hc, EK⟩ := H
  have HKmin : ∀ k, K e k → ck ≤ k := by
    intro k HK
    have HH := hmin n cb e k R HK
    omega
  have HMnext : PiInertTypedContinuationMinimum D Ω out Ξ
      (ProofShape.mkApps ((plug e).subst τ) args) ck := by
    refine ⟨K', suffixStage, cs, ck', e', HTnext, RS, HR, hc, ?_⟩
    intro later j endpoint k RJ HK
    exact HKmin (j+k) ((EK e (j+k)).2 ⟨later, j, endpoint, k, rfl, RJ, HK⟩)
  refine ⟨Θ, Ξ, τ, args, plug, suffixStage, cs, e', ck', K', HP, W, HTplug, HTnext, RS, HR,
    by omega, HMnext, ?_⟩
  intro bodyStage tailStage j endpoint l tail k RJ RK HK
  have HH := hmin bodyStage j endpoint (l+k) RJ
    ((EK endpoint (l+k)).2 ⟨tailStage, l, tail, k, rfl, RK, HK⟩)
  omega

/-- Following a typed minimum either already reaches a carrier at its current
endpoint, or finds the next actual application behind a finite retained-lambda
prefix. The next scope has a minimum of at most the original count, strictly
smaller when the preceding body path has positive count. Equal-count moves
are not claimed to finish the recursive eta argument. -/
theorem PiInertTypedContinuationMinimum.advance
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost)
    (HE : CarrierExposure out) :
    ∃ K n cb ck e, TypedSource Δ source ∧
      ScopedComputeCount (PiInertStage D n) cb Δ source e ∧
      PiInertTypedContinuationRun D Ω out Δ K e ck ∧ cb+ck = cost ∧
      (CarrierExposure e ∨
        (PiInertNextApplication D Ω out Δ K e ck ∧
          ∃ Θ Ξ τ args plug, PiInertRetainedPrefix D Δ Θ plug ∧ PiInertEndpointMap Θ Ξ τ ∧
            TypedSource Θ (plug e) ∧ PiInertTypedContinuationMinimum D Ω out Ξ
              (ProofShape.mkApps ((plug e).subst τ) args) ck)) ∧
      ck ≤ cost ∧ (0 < cb → ck < cost) ∧
      ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint →
        K endpoint k → cost ≤ j+k := by
  classical
  obtain ⟨K, n, cb, ck, e, HT, R, HR, hc, HM⟩ := H
  refine ⟨K, n, cb, ck, e, HT, R, HR, hc, ?_, by omega, (by omega), HM⟩
  by_cases he : CarrierExposure e
  · exact .inl he
  · have HA := HR.next_application HE he
    refine .inr ⟨HA, HA.minimum ?_⟩
    intro k HK
    have HH := HM n cb e k R HK
    omega

/-- A fixed constant remains at the head after discarding any surrounding
application nodes and retained lambda binders. Arguments and annotations are
unrestricted. This syntactic invariant is stable under arbitrary endpoint
substitution and beta reduction, unlike native recovery certificates. -/
inductive RetainedConstHead (c : Name) : ProofShape → Prop where
  | const : RetainedConstHead c (.const c ls)
  | app : RetainedConstHead c f → RetainedConstHead c (.app f a)
  | lam : RetainedConstHead c b → RetainedConstHead c (.lam A b)

omit [Params] in
/-- Supplying arbitrary pending arguments retains the fixed constant. -/
theorem RetainedConstHead.mkApps (H : RetainedConstHead c f) (args : List ProofShape) :
    RetainedConstHead c (ProofShape.mkApps f args) := by
  induction args generalizing f with
  | nil => exact H
  | cons a args ih => exact ih (.app H)

omit [Params] in
/-- Substitution changes only arguments, annotations and variable occurrences;
the tracked head constant cannot be replaced. -/
theorem RetainedConstHead.subst (H : RetainedConstHead c e) (τ : ProofShape.Subst) :
    RetainedConstHead c (e.subst τ) := by
  induction H generalizing τ with
  | const => exact .const
  | app _ ih => exact .app (ih τ)
  | lam _ ih => exact .lam (ih τ.lift)

omit [Params] in
/-- Beta reduction can consume retained lambdas but preserves the tracked
constant in their bodies. No typing or guarded-substitution law is used. -/
theorem RetainedConstHead.beta (H : RetainedConstHead c e) (R : BetaRed e e') :
    RetainedConstHead c e' := by
  induction R with
  | refl => exact H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ih _ => cases H with | app H => exact .app (ih H)
  | proj => cases H
  | lam _ _ _ ih => cases H with | lam H => exact .lam (ih H)
  | forallE => cases H
  | beta =>
    cases H with | app H => cases H with | lam H =>
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H.subst (ProofShape.Subst.one _)

omit [Params] in
/-- A tracked constant is either already the ordinary spine head or is
protected by a retained lambda at that head. -/
theorem RetainedConstHead.spine_form (H : RetainedConstHead c e) :
    e.constHead = some c ∨ ∃ A b args, e = ProofShape.mkApps (.lam A b) args := by
  induction H with
  | const => exact .inl rfl
  | app _ ih =>
    rcases ih with HE | ⟨A, b, args, rfl⟩
    · exact .inl HE
    · exact .inr ⟨A, b, args ++ [_], (ProofShape.mkApps_snoc ..).symm⟩
  | lam => exact .inr ⟨_, _, [], rfl⟩

/-- A retained Eq recursor cannot itself expose a carrier, even beneath
arbitrary retained lambdas and applications. -/
theorem RetainedConstHead.eq_not_exposed (heq : env.HasCanonicalEq)
    (H : RetainedConstHead ``Eq.rec e) : ¬ CarrierExposure e := by
  intro HE
  rcases H.spine_form with HC | ⟨A, b, args, EE⟩
  · exact carrier_exposure_ne_eqRec heq HE HC
  · exact HE.not_lambda_spine A b args EE

/-- An actual continuation of zero primitive cost preserves the fixed
constant through every application substitution and retained lambda frame.
Annotation costs in retained frames are immaterial to this head invariant. -/
theorem PiInertTypedContinuationRun.zero_head
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck)
    (hc : ck = 0) (HE : RetainedConstHead c e) : RetainedConstHead c out := by
  induction H with
  | terminal => exact HE
  | application _ _ _ R _ ih =>
    have R0 := R
    have hz : _ = 0 := Nat.eq_zero_of_add_eq_zero_right hc
    rw [hz] at R0
    apply ih (Nat.eq_zero_of_add_eq_zero_left hc)
    exact ((HE.subst _).mkApps _).beta R0.zero_beta
  | retained _ _ _ _ _ ih => exact ih hc ((RetainedConstHead.lam HE).mkApps _)

/-- The global count induction has no zero-cost Eq case, including arbitrary
mixed typed continuation frames. A beta-only body and continuation retain the
Eq head and therefore cannot reach the exposed final output. -/
theorem PiInertTypedContinuationMinimum.eq_positive
    (heq : env.HasCanonicalEq)
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost)
    (HC : RetainedConstHead ``Eq.rec source) (HE : CarrierExposure out) : 0 < cost := by
  obtain ⟨K, n, cb, ck, e, _, R, HR, hc, _⟩ := H
  by_contra hn
  have hb : cb = 0 := by omega
  have hk : ck = 0 := by omega
  rw [hb] at R
  exact (HR.zero_head hk (HC.beta R.zero_beta)).eq_not_exposed heq HE

end Lean4Lean.VEnv.Strengthening
