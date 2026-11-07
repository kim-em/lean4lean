import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldCutActivation

/-! # Preserve the supplying argument through further eta frames

A distinguished future application consumes the temporary type binder with
one fixed argument at a base context independent of the final observer. Further retained and consuming frames live above that
binder. Both eta branches preserve this application and its exact argument,
while ordinary projection-frame minima are recovered by forgetting the mark.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- An actual projection continuation with a distinguished future consumption
of `A` by `x`. Every preceding frame stays above `A :: Δ`; it may retain or
consume other temporary binders. `Ω` is the final observer; `Δ` is the
base where the distinguished argument is supplied. The selected final projection and all raw
competitor predicates are unchanged. `controls` records the current temporary
binders above the distinguished one, not a replacement context for them. -/
inductive PiInertFreshFieldRun (D : Definitions) (Ω Δ : List ProofShape)
    (family : Name) (out A x : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Nat → Prop where
  | supply : TypedSource (A :: Δ) e →
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) →
      TypedSource Δ (ProofShape.mkApps (e.subst (ProofShape.Subst.one x)) args) →
      ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (e.subst (ProofShape.Subst.one x)) args) endpoint →
      PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames →
      PiInertFreshFieldRun D Ω Δ family out A x []
        (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) args K) e (cs+ck) (frames+1)
  | application : TypedSource (controls ++ A :: Δ) e →
      PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ →
      TypedSource (nextControls ++ A :: Δ) (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs (nextControls ++ A :: Δ)
        (ProofShape.mkApps (e.subst τ) args) endpoint →
      PiInertFreshFieldRun D Ω Δ family out A x nextControls K endpoint ck frames →
      PiInertFreshFieldRun D Ω Δ family out A x controls
        (PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ args K) e (cs+ck) (frames+1)
  | retained : TypedSource (C :: (controls ++ A :: Δ)) body →
      DomainSort (controls ++ A :: Δ) C v →
      ScopedComputeCount (PiInertStage D n) cd (controls ++ A :: Δ) C C' →
      ContextSubstitution (C :: (controls ++ A :: Δ)) (C' :: (controls ++ A :: Δ)) ProofShape.Subst.id →
      PiInertFreshFieldRun D Ω Δ family out A x controls K (ProofShape.mkApps (.lam C' body) args) ck frames →
      PiInertFreshFieldRun D Ω Δ family out A x (C :: controls)
        (fun body k => K (ProofShape.mkApps (.lam C' body) args) k) body ck (frames+1)

/-- Forget which application supplies the original type argument, preserving
its exact computation, raw continuation predicate, cost and frame count. -/
theorem PiInertFreshFieldRun.forget
    (H : PiInertFreshFieldRun D Ω Δ family out A x controls K e ck frames) :
    PiInertProjectionRunFrames D Ω family 0 out (controls ++ A :: Δ) K e ck frames := by
  induction H with
  | supply HT W HNext RNext HK => exact .application HT (.inst W) HNext RNext HK
  | application HT W HNext RNext _ ih => exact .application HT W HNext RNext ih
  | retained HT SD RD WI _ ih => exact .retained HT SD RD WI ih

/-- An application strictly above the distinguished binder preserves its
fresh-field variable exactly. The supplied argument is not activated until
the distinguished application itself. This follows from the actual endpoint
map and the literal context suffix, not a condition imposed on competitors. -/
theorem PiInertEndpointMap.fresh_field
    (W : PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ) :
    (ProofShape.bvar controls.length).subst τ = .bvar nextControls.length := by
  obtain ⟨rest, E, _, EF⟩ := W.observer_tail (Ω := A :: Δ) rfl (by simp)
  have hlen := congrArg List.length E
  simp only [List.length_append] at hlen
  have hh : rest.length = nextControls.length := by omega
  have HE := EF (.bvar 0) 0
  simpa only [Nat.zero_add, ProofShape.Subst.liftN, ProofShape.liftN, liftVar,
    Nat.lt_irrefl, ↓reduceIte, Nat.add_zero, hh] using HE

/-- A minimum retaining the selected future type-binder application.
Competitors still range over all raw endpoints and finite stages, with exactly
the existing continuation predicate. No competing-path provenance is required. -/
def PiInertFreshFieldMinimum (D : Definitions) (Ω Δ : List ProofShape)
    (family : Name) (out A x : ProofShape) (controls : List ProofShape)
    (source : ProofShape) (cost frames : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource (controls ++ A :: Δ) source ∧
    ScopedComputeCount (PiInertStage D n) cb (controls ++ A :: Δ) source endpoint ∧
    PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames ∧ cb+ck = cost ∧
    ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ) source tail →
      K tail k → cost ≤ j+k

/-- The marked minimum is an ordinary projection minimum with the same
selected frame count and no change to its competitor quantification. -/
theorem PiInertFreshFieldMinimum.forget
    (H : PiInertFreshFieldMinimum D Ω Δ family out A x controls source cost frames) :
    PiInertProjectionFrameMinimum D Ω family 0 out (controls ++ A :: Δ) source cost frames := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, R, HK.forget, hc, HM⟩

/-- Both actual eta branches retain the distinguished future supply of `x`.
A retained lambda adds a retained frame; a consumed lambda adds its actual
application above the distinguished binder. The child minimum has strictly
smaller primitive count, precisely one additional frame, and the same `x`.
The actual argument-origin decomposition is the existing checked eta cut. -/
theorem CountedEtaFrameOrigin.fresh_field_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaFrameOrigin D n (controls ++ A :: Δ) f C v args endpoint ct ck cost K)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames) :
    ∃ smaller, smaller < cost ∧ PiInertFreshFieldMinimum D Ω Δ family out A x (C :: controls)
      (.app (f.liftN 1) (etaArgument v)) smaller (frames+1) := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨C', body', args', cf, ca, cd, cb, m, _, _, EO, _, _, RD, HT, RB, hsmall, HM⟩ |
    ⟨C', body', x', xs', cf, ca, cs, cd, cb, m, _, _, _, _, _, HT, RB, WI, HTnext, RS, hsmall, HM⟩
  · have HR : PiInertFreshFieldRun D Ω Δ family out A x controls K
        (ProofShape.mkApps (.lam C' body') args') ck frames := by simpa only [EO] using HK
    refine ⟨cb+ck, hsmall, (fun body k => K (ProofShape.mkApps (.lam C' body) args') k),
      m, cb, ck, body', HT, RB, ?_, rfl, HM⟩
    exact .retained (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HR
  · have RT : ScopedComputeCount (PiInertStage D n) cs (controls ++ A :: Δ)
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') endpoint := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have Hnext : TypedSource (controls ++ A :: Δ)
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    refine ⟨cb+(cs+ck), by omega,
      PiInertApplicationContinuation D (controls ++ A :: Δ) (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HT, RB, ?_, rfl, ?_⟩
    · exact .application (HT.pi_inert_compute heq hs RB.forget) (.inst WI) Hnext RT HK
    · intro later j tail k RJ RK
      have HH := HM later j tail k RJ RK
      omega

/-- A native eta selected in a marked minimum descends with its exact future
supplying argument intact. Repeating this theorem allows arbitrarily many
consumed or retained eta frames above that one fixed binder. It does not yet
establish constructor-field readout through the resulting smaller minimum. -/
theorem pi_inert_eta_fresh_field_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource (controls ++ A :: Δ) (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard (controls ++ A :: Δ) f (.forallE C B))
    (SD : DomainSort (controls ++ A :: Δ) C v)
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) original (ProofShape.mkApps f args))
    (HR : PiInertStage D n (controls ++ A :: Δ) f (.lam C (.app (f.liftN 1) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam C (.app (f.liftN 1) (etaArgument v))) args) endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      original endpoint' → K endpoint' k → cost ≤ j+k) :
    ∃ smaller, smaller < cost ∧ PiInertFreshFieldMinimum D Ω Δ family out A x (C :: controls)
      (.app (f.liftN 1) (etaArgument v)) smaller (frames+1) := by
  have H := pi_inert_eta_frame_origin heq hs hguard HT RN SD RP HR RT HK.forget.forget.holds hcost HM
  exact H.fresh_field_minimum heq hs HK

end Lean4Lean.VEnv.Strengthening
