import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedContinuation

/-! # Typed eta continuations ending in a projection

The observer keeps its result fixed while allowing its major to vary. Counts
include the final projection computation. Eta descent retains this observer
through actual substitutions, pending applications and surviving lambdas.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A final projection at any finite stage. Competitors need no typing
certificate and may change the major as well as the finite stage. -/
def PiInertProjectionContinuation (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out e : ProofShape) (cost : Nat) : Prop :=
  ∃ n, ScopedComputeCount (PiInertStage D n) cost Ω (.proj family index e) out

/-- Actual typed frames ending in a projection computation. Only the selected
execution carries typings; the underlying predicates admit all raw competitors.
The endpoint maps are identity or consumption of one actual binder. -/
inductive PiInertProjectionContinuationRun (D : Definitions) (Ω : List ProofShape) (family : Name) (index : Nat) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Prop where
  | projection : TypedSource Ω e → TypedSource Ω (.proj family index e) →
      ScopedComputeCount (PiInertStage D n) ck Ω (.proj family index e) out →
      PiInertProjectionContinuationRun D Ω family index out Ω
        (PiInertProjectionContinuation D Ω family index out) e ck
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertProjectionContinuationRun D Ω family index out Θ K e' ck →
      PiInertProjectionContinuationRun D Ω family index out Δ (PiInertApplicationContinuation D Θ τ args K) e (cs+ck)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertProjectionContinuationRun D Ω family index out Δ K (ProofShape.mkApps (.lam A' body) args) ck →
      PiInertProjectionContinuationRun D Ω family index out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck

/-- The chosen execution satisfies its original continuation predicate at
exactly the recorded count. -/
theorem PiInertProjectionContinuationRun.holds
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck) : K e ck := by
  induction H with
  | projection _ _ R => exact ⟨_, R⟩
  | application _ _ _ R _ ih => exact ⟨_, _, _, _, rfl, R, ih⟩
  | retained _ _ _ _ _ ih => exact ih

/-- Every chosen incoming endpoint has an actual typed realization in its
current scope, including bodies under retained original annotations. -/
theorem PiInertProjectionContinuationRun.typed
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck) : TypedSource Δ e := by
  cases H with
  | projection HT => exact HT
  | application HT => exact HT
  | retained HT => exact HT

/-- A minimum with an actual typed execution of its continuation. The minimum
still ranges over all endpoints and stages satisfying the same raw predicate,
not just over competitors that carry an execution or typing certificate. -/
def PiInertProjectionContinuationMinimum (D : Definitions) (Ω : List ProofShape) (family : Name) (index : Nat) (out : ProofShape)
    (Δ : List ProofShape) (source : ProofShape) (cost : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertProjectionContinuationRun D Ω family index out Δ K endpoint ck ∧ cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- The actual eta cut preserves a typed continuation execution in both
branches. For consumption, its newly retained suffix-source typing supplies
the application constructor. For a surviving lambda, the old execution types
the enclosing long endpoint and body computation types its new input. -/
theorem CountedEtaContinuationCut.projection_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaContinuationCut D n Δ f A u args endpoint ct ck cost K)
    (HK : PiInertProjectionContinuationRun D Ω family index out Δ K endpoint ck) :
    ∃ smaller, smaller < cost ∧
      PiInertProjectionContinuationMinimum D Ω family index out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, _, EO, _, _, _, cd, cb, m, _, hsmall, HT, RD, RB, _, HM⟩ |
    ⟨body', x', xs', cb, cs, m, hsmall, HT, WI, RB, RS, HTnext, _, _, HM⟩
  · have HR : PiInertProjectionContinuationRun D Ω family index out Δ K
        (ProofShape.mkApps (.lam A' body') args') ck := by simpa only [EO] using HK
    refine ⟨cb+ck, hsmall, (fun body k => K (ProofShape.mkApps (.lam A' body) args') k),
      m, cb, ck, body', HT, RB, ?_, rfl, HM⟩
    exact .retained (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HR
  · have RT : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') endpoint := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have Hnext : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    refine ⟨cb+(cs+ck), by omega,
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HT, RB, ?_, rfl, ?_⟩
    · exact .application (HT.pi_inert_compute heq hs RB.forget) (.inst WI) Hnext RT HK
    · intro later j endpoint' k RJ RK
      have HH := HM later j endpoint' k RJ RK
      omega

/-- The actual native eta induction step retains typed continuation execution
and strictly decreases the same global count. The required new application
source typing is derived in the cut theorem, not supplied by the caller. -/
theorem pi_inert_eta_projection_continuation_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (HK : PiInertProjectionContinuationRun D Ω family index out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ∃ smaller, smaller < cost ∧
      PiInertProjectionContinuationMinimum D Ω family index out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller :=
  (pi_inert_eta_continuation_cut heq hs hguard HT RN SD RP HR RT HK.holds hcost hmin).projection_frames heq hs HK


/-- Seed eta descent from a global minimum of the full projected computation.
Unlike a minimum to a fixed major, this allows a competitor to change the
major provided its projection still computes to the same observed output. -/
theorem pi_inert_eta_projected_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (HTproj : TypedSource Δ (.proj family index original))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (RF : ScopedComputeCount (PiInertStage D tailStage) ck Δ (.proj family index endpoint) out)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family index original) out → cost ≤ j) :
    ∃ smaller, smaller < cost ∧
      PiInertProjectionContinuationMinimum D Δ family index out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  have Reta := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := args))
  have HTend := HT.pi_inert_compute heq hs (Reta.trans RT).forget
  have HTobs := HTproj.pi_inert_compute heq hs ((RP.trans Reta).trans RT).proj.forget
  apply pi_inert_eta_projection_continuation_frames heq hs hguard HT RN SD RP HR RT
    (PiInertProjectionContinuationRun.projection HTend HTobs RF) hcost
  rintro later j endpoint' k RJ ⟨observerStage, RK⟩
  have RC := (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later observerStage))).proj.trans
    (RK.mono (pi_inert_stage_mono (Nat.le_max_right later observerStage)))
  exact hmin _ _ RC

end Lean4Lean.VEnv.Strengthening
