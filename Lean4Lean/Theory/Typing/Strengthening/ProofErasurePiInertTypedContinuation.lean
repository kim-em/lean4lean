import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertContinuationFrames

/-! # Actual typed executions of the concrete continuation frames

Retain typing at each actual application source, rather than only the typed
substitution between scopes, including whether it is identity or consumption
of one actual binder. The eta minimum step supplies this data from its
actual computation, including the exact source of the suffix after beta.
Competitor paths remain unconstrained by these typing witnesses.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The endpoint maps actually constructed by eta consumption and hole
focusing. Consumption removes exactly the displayed source binder; identity
focusing stays in the same scope. The ordinary typed interpretation is retained
in each case, but arbitrary context maps are not constructors. -/
inductive PiInertEndpointMap : List ProofShape → List ProofShape → ProofShape.Subst → Prop where
  | identity : ContextSubstitution Δ Δ ProofShape.Subst.id →
      PiInertEndpointMap Δ Δ ProofShape.Subst.id
  | inst : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) →
      PiInertEndpointMap (A :: Δ) Δ (ProofShape.Subst.one x)

/-- Forget only the origin of the actual endpoint map. -/
theorem PiInertEndpointMap.interpretation (H : PiInertEndpointMap Δ Θ τ) :
    ContextSubstitution Δ Θ τ := by
  cases H with
  | identity W | inst W => exact W

/-- Identity or a single actual binder consumption beneath finitely many
retained binders. This is a syntactic restriction, not target agreement. -/
def SingleEndpointSubstitution (τ : ProofShape.Subst) : Prop :=
  τ = ProofShape.Subst.id ∨ ∃ x depth, τ = (ProofShape.Subst.one x).liftN depth

omit [Params] in
/-- Entering one more retained binder preserves the single-consumption form. -/
theorem SingleEndpointSubstitution.lift (H : SingleEndpointSubstitution τ) :
    SingleEndpointSubstitution τ.lift := by
  rcases H with rfl | ⟨x, depth, rfl⟩
  · exact .inl ProofShape.Subst.id_lift
  · exact .inr ⟨x, depth+1, rfl⟩

omit [Params] in
/-- A finite retained prefix only changes the depth of the same consumption. -/
theorem SingleEndpointSubstitution.liftN (H : SingleEndpointSubstitution τ) (depth : Nat) :
    SingleEndpointSubstitution (τ.liftN depth) := by
  induction depth with
  | zero => exact H
  | succ depth ih => exact ih.lift

/-- Every actual application frame supplies the restricted raw map. -/
theorem PiInertEndpointMap.single (H : PiInertEndpointMap Δ Θ τ) :
    SingleEndpointSubstitution τ := by
  cases H with
  | identity => exact .inl rfl
  | inst => exact .inr ⟨_, 0, rfl⟩

/-- An actual execution of a finite continuation, carrying its chosen paths
and typings. The underlying predicate still admits the same competitors;
these witnesses describe only the selected execution. In an application
frame, both the incoming endpoint and the full substituted application source
are typed. A retained frame carries typing of its body in the original scope. -/
inductive PiInertTypedContinuationRun (D : Definitions) (Ω : List ProofShape) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Prop where
  | terminal : TypedSource Ω out →
      PiInertTypedContinuationRun D Ω out Ω (fun e k => e = out ∧ k = 0) out 0
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertTypedContinuationRun D Ω out Θ K e' ck →
      PiInertTypedContinuationRun D Ω out Δ (PiInertApplicationContinuation D Θ τ args K) e (cs+ck)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertTypedContinuationRun D Ω out Δ K (ProofShape.mkApps (.lam A' body) args) ck →
      PiInertTypedContinuationRun D Ω out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck

/-- Forget the actual execution while retaining precisely its concrete frame
predicate. No competitor restriction is introduced by the added typing data. -/
theorem PiInertTypedContinuationRun.frames
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck) :
    PiInertContinuationFrames D Ω out Δ K := by
  induction H with
  | terminal => exact .terminal
  | application _ W _ _ _ ih => exact .application W.interpretation ih
  | retained _ SD RD WI _ ih => exact .retained SD RD WI ih

/-- The chosen execution satisfies its original continuation predicate at
exactly the recorded count. -/
theorem PiInertTypedContinuationRun.holds
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck) : K e ck := by
  induction H with
  | terminal => exact ⟨rfl, rfl⟩
  | application _ _ _ R _ ih => exact ⟨_, _, _, _, rfl, R, ih⟩
  | retained _ _ _ _ _ ih => exact ih

/-- Every chosen incoming endpoint has an actual typed realization in its
current scope, including bodies under retained original annotations. -/
theorem PiInertTypedContinuationRun.typed
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck) : TypedSource Δ e := by
  cases H with
  | terminal HT => exact HT
  | application HT => exact HT
  | retained HT => exact HT

/-- A minimum with an actual typed execution of its continuation. The minimum
still ranges over all endpoints and stages satisfying the same raw predicate,
not just over competitors that carry an execution or typing certificate. -/
def PiInertTypedContinuationMinimum (D : Definitions) (Ω : List ProofShape) (out : ProofShape)
    (Δ : List ProofShape) (source : ProofShape) (cost : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertTypedContinuationRun D Ω out Δ K endpoint ck ∧ cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- The enriched minimum implies the existing concrete continuation minimum
with exactly the same source, endpoint choices and competitor predicate. -/
theorem PiInertTypedContinuationMinimum.forget
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost) :
    PiInertContinuationMinimum D Ω out Δ source cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HR, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HR.frames, HT, R, HR.holds, hc, HM⟩

/-- The actual eta cut preserves a typed continuation execution in both
branches. For consumption, its newly retained suffix-source typing supplies
the application constructor. For a surviving lambda, the old execution types
the enclosing long endpoint and body computation types its new input. -/
theorem CountedEtaContinuationCut.typed_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaContinuationCut D n Δ f A u args endpoint ct ck cost K)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck) :
    ∃ smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Ω out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, _, EO, _, _, _, cd, cb, m, _, hsmall, HT, RD, RB, _, HM⟩ |
    ⟨body', x', xs', cb, cs, m, hsmall, HT, WI, RB, RS, HTnext, _, _, HM⟩
  · have HR : PiInertTypedContinuationRun D Ω out Δ K
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
theorem pi_inert_eta_typed_continuation_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ∃ smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Ω out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller :=
  (pi_inert_eta_continuation_cut heq hs hguard HT RN SD RP HR RT HK.holds hcost hmin).typed_frames heq hs HK

/-- Seed the typed continuation invariant directly from the selected native
eta in a whole-path minimum. Its actual eta/suffix path derives terminal
output typing, so no additional endpoint-typing assumption is required. -/
theorem pi_inert_eta_terminal_typed_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) out)
    (hcost : cp+1+ct ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ original out → cost ≤ j) :
    ∃ smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Δ out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  have HTout := HT.pi_inert_compute heq hs
    ((((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := args))).trans RT).forget)
  apply pi_inert_eta_typed_continuation_frames heq hs hguard HT RN SD RP HR RT
    (PiInertTypedContinuationRun.terminal HTout) (by omega)
  rintro later j endpoint k RJ ⟨rfl, rfl⟩
  simpa only [Nat.add_zero] using hmin later j RJ

/-- Preserve the typed execution through the actual inner eta already
selected by the Eq body cut. The enclosing instantiation's application typing
comes from the original outer eta/lambda/argument/beta path. Thus the smaller
minimum under both binders needs no new later-source typing hypothesis. -/
theorem CountedEtaBodySpineCut.nested_eta_typed_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (HRouter : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct (EqEtaRemainingRoot D))
    (hcost : cp+1+ct ≤ cost) :
    ∃ innerA innerU bodyLs bodyPre smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Δ out (innerA :: A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) smaller := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, _, _, _, RP, HR, _, RT, _, HM, _, _, WI, _, k, _, HEta⟩ := H
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have HTwhole : TypedSource (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls') bodyPre) bodyPending) := by
    simpa only [ProofShape.mkApps_append] using HTbody.pi_inert_compute heq hs RP.forget
  have HTbody' := HTwhole.pi_inert_compute heq hs
    ((((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).trans RT).forget)
  have HTlong := HT.pi_inert_compute heq hs
    (((ScopedComputeCount.base HRouter).mkApps (ScopedArgumentsCount.refl (args := args))).forget)
  have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  have HTnext := HTlong.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
  have HTout := HTnext.pi_inert_compute heq hs RS.forget
  have HK : PiInertTypedContinuationRun D Δ out (A :: Δ)
      (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs'
        (fun e k => e = out ∧ k = 0)) body' cs := by
    have RS' : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') out := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    simpa only [Nat.add_zero] using
      PiInertTypedContinuationRun.application HTbody' (.inst WI) HTnext' RS' (.terminal HTout)
  cases HEta with
  | @intro innerA innerB innerU RNinner SDinner =>
    obtain ⟨smaller, hsmall, Htyped⟩ := pi_inert_eta_typed_continuation_frames heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RNinner SDinner
      (by simpa only [ProofShape.mkApps_append] using RP) HR RT HK
      (cost := cb+cs) (by omega) (by
        rintro later j endpoint suffixCost RJ ⟨suffixStage, suffixCount, endpoint', tailCost, hsum, RK, rfl, rfl⟩
        have HH := HM later suffixStage j suffixCount endpoint RJ
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RK)
        omega)
    exact ⟨innerA, innerU, ls', bodyPre, smaller, by omega, Htyped⟩

end Lean4Lean.VEnv.Strengthening
