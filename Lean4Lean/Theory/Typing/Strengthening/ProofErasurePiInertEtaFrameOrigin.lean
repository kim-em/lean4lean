import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedContinuation

/-! # Retain actual argument origins at an eta minimum step

Both branches retain the exact lambda, annotation, body and argument paths.
In particular a consumed frame keeps the argument computation that produced
its substitution image; a context interpretation alone would lose that origin.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

/-- The actual retained or consumed eta decomposition, including its child
minimum with the exact induced continuation predicate. The consumed branch
keeps the original argument-vector computation, not only its typed substitution.
Target agreement still has to be derived from the parent's whole completion. -/
def CountedEtaFrameOrigin (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (f A : ProofShape) (u : VLevel) (args : List ProofShape) (endpoint : ProofShape)
    (ct ck cost : Nat) (K : ProofShape → Nat → Prop) : Prop :=
  DomainSort Δ A u ∧ (
  (∃ A' body' args' cf ca cd cb m, cf+ca ≤ ct ∧ cd+cb = cf ∧
    endpoint = ProofShape.mkApps (.lam A' body') args' ∧
    ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app (f.liftN 1) (etaArgument u))) (.lam A' body') ∧
    ScopedArgumentsCount (PiInertStage D n) Δ ca args args' ∧
    ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
    ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body' ∧ cb+ck < cost ∧
    ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body →
      K (ProofShape.mkApps (.lam A' body) args') k → cb+ck ≤ j+k) ∨
  (∃ A' body' x' xs' cf ca cs cd cb m, cf+ca+cs ≤ ct ∧ cd+cb = cf ∧
    ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app (f.liftN 1) (etaArgument u))) (.lam A' body') ∧
    ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
    ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
    ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body' ∧
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
    TypedSource Δ (ProofShape.mkApps (body'.inst x') xs') ∧
    ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') endpoint ∧ cb+cs+ck < cost ∧
    ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) body →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K body k → cb+cs+ck ≤ j+k))

/-- Derive the origin from the actual parent suffix. The child minimum uses
precisely the same body endpoint and the actual retained or consumed argument
vector. All computations remain in their original scopes. -/
theorem pi_inert_eta_frame_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (HK : K endpoint ck) (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    CountedEtaFrameOrigin D n Δ f A u args endpoint ct ck cost K := by
  have HTlong := HT.pi_inert_compute heq hs
    (((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := args))).forget)
  have HTbody : TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) :=
    (ScopedHole.lamBody A .hole).typed (typed_spine_head HTlong)
  refine ⟨SD, ?_⟩
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    obtain ⟨_, hsmall, HM⟩ := pi_inert_retained_lambda_continuation_minimal_of
      RP HR RD RB RX (EO ▸ HK) (by omega) hmin
    exact .inl ⟨A', body', args', cf, ca, cd, cb, m, hc, hsplit, EO,
      RF, RX, RD, HTbody, RB, hsmall, HM⟩
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    obtain ⟨_, hsmall, HM⟩ := pi_inert_counted_lambda_continuation_minimal_of
      RP HR RD RB RX RS HK (by omega) hmin
    obtain ⟨_, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
        (ProofShape.mkApps (.lam A' body') (x' :: xs'))
        (ProofShape.mkApps (body'.inst x') xs') := by
      simpa only [ProofShape.mkApps] using
        (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
          (ScopedArgumentsCount.refl (args := xs'))
    have HTnext := HTlong.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
    exact .inr ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, hc, hsplit,
      RF, RX, RD, HTbody, RB, WI, HTnext, RS, hsmall, HM⟩

/-- The recorded origin supplies the usual smaller typed minimum. Its new
continuation is built from the exact stored branch and body endpoint. The
origin itself remains available to reconstruct argument agreement later. -/
theorem CountedEtaFrameOrigin.typed_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaFrameOrigin D n Δ f A u args endpoint ct ck cost K)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck) :
    ∃ smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Ω out (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, cd, cb, m, _, _, EO, _, _, RD, HT, RB, hsmall, HM⟩ |
    ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, _, _, _, _, _, HT, RB, WI, HTnext, RS, hsmall, HM⟩
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

end Lean4Lean.VEnv.Strengthening
