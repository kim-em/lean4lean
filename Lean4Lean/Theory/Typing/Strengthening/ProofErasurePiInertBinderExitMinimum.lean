import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPairObserverSort

/-! # Focus the first binder exit of a closed pair minimum

Identity frames at a closed record have no pending arguments. Their actual
computations can be combined with the body prefix, while competitors are
reinserted at zero body cost. With exactly one extra binder, the first remaining
frame consumes it or retains its lambda; the count and minimum stay exact.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- The first frame that leaves the displayed binder, after all preceding
identity frames have been folded into the actual body path. Both alternatives
retain global minimality against arbitrary raw competitors. Retained-frame
readout and recursive native eta after consumption remain open. -/
inductive PiInertBinderExitMinimum (D : Definitions) (Δ : List ProofShape)
    (family : Name) (out A source : ProofShape) (cost : Nat) : Prop where
  | consumed
      (HT : TypedSource (A :: Δ) source)
      (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) source endpoint)
      (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
      (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) args))
      (RS : ScopedComputeCount (PiInertStage D suffixStage) cs Δ
        (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) args) next)
      (HK : PiInertProjectionContinuationRun D Δ family 0 out Δ K next ck)
      (hcost : cb+cs+ck = cost)
      (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint' →
        PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) args K endpoint' k → cost ≤ j+k) :
      PiInertBinderExitMinimum D Δ family out A source cost
  | retained
      (HT : TypedSource (A :: Δ) source)
      (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) source body)
      (SD : DomainSort Δ A u)
      (RD : ScopedComputeCount (PiInertStage D domainStage) cd Δ A A')
      (WI : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id)
      (HK : PiInertProjectionContinuationRun D Δ family 0 out Δ K
        (ProofShape.mkApps (.lam A' body) args) ck)
      (hcost : cb+ck = cost)
      (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint' →
        K (ProofShape.mkApps (.lam A' endpoint') args) k → cost ≤ j+k) :
      PiInertBinderExitMinimum D Δ family out A source cost

/-- Identity frames cannot hide a missing binder exit. Actual closed-record
typing forces their pending arguments to be empty, so their computations move
into the body prefix with exact cost and unchanged global minimality. -/
theorem PiInertProjectionContinuationRun.closed_record_binder_exit
    (H : PiInertProjectionContinuationRun D Ω family 0 out Ξ K endpoint ck)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hscope : Ξ = A :: Ω)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Ξ)
    (hm : env.HasType univs Γ m (.const family [])) (Es : proofErase Γ m = source)
    (RB : ScopedComputeCount (PiInertStage D n) cb Ξ source endpoint)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint' →
      K endpoint' k → cb+ck ≤ j+k) :
    PiInertBinderExitMinimum D Ω family out A source (cb+ck) := by
  induction H generalizing A Γ m source n cb with
  | projection =>
    have HL := congrArg List.length hscope
    simp only [List.length_cons] at HL
    omega
  | @application Ξ e Θ τ args frameStage cs e' K ck HT W HNext RNext HK ih =>
    cases W with
    | identity =>
      obtain ⟨m', HE, Em'⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
        hΓ hm EΓ Es RB.forget
      have EN := TypedSource.closed_record_pending_nil hi hΓ EΓ HE.hasType.2
        (by simpa only [ProofShape.subst_id, ← Em'] using HNext)
      have RNext' : ScopedComputeCount (PiInertStage D frameStage) cs Ξ e e' := by
        simpa only [EN, ProofShape.mkApps, ProofShape.subst_id] using RNext
      have RB' := (RB.mono (pi_inert_stage_mono (Nat.le_max_left n frameStage))).trans
        (RNext'.mono (pi_inert_stage_mono (Nat.le_max_right n frameStage)))
      have HM' : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint' →
          K endpoint' k → (cb+cs)+ck ≤ j+k := by
        intro later j endpoint' k RJ RK
        have RJ' : ScopedComputeCount (PiInertStage D later) j Ξ
            (ProofShape.mkApps (source.subst ProofShape.Subst.id) args) endpoint' := by
          simpa only [EN, ProofShape.mkApps, ProofShape.subst_id] using RJ
        have HH := HM later 0 source (j+k) (.beta .refl) ⟨later, j, endpoint', k, rfl, RJ', RK⟩
        omega
      simpa only [Nat.add_assoc] using ih hscope hΓ EΓ hm Es RB' HM'
    | inst W =>
      cases hscope
      exact .consumed ⟨Γ, m, _, hΓ, EΓ, hm, Es⟩ RB W HNext RNext HK (by omega) HM
  | retained HT SD RD WI HK ih =>
    cases hscope
    exact .retained ⟨Γ, m, _, hΓ, EΓ, hm, Es⟩ RB SD RD WI HK rfl HM

/-- Any actual minimum on a closed pair under one extra binder has a concrete
consuming or retained exit, even when arbitrarily many identity frames precede
it. This supplies the frame decomposition rather than asking a caller for it. -/
theorem PiInertProjectionContinuationMinimum.pair_binder_exit
    (H : PiInertProjectionContinuationMinimum D Δ family 0 out (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) fields) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hz : info.nindices = 0)
    (hlen : fields.length = info.numFields) :
    PiInertBinderExitMinimum D Δ family out A
      (ProofShape.mkApps (.const info.ctorName []) fields) cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  obtain ⟨Γ, m, hΓ, EΓ, hm, Es⟩ := TypedSource.closed_constructor_realize hi hp hz hlen HT
  subst cost
  exact HK.closed_record_binder_exit heq hs hi rfl hΓ EΓ hm Es RB HM


/-- The weighted first structure root actually supplies the binder-exit
configuration, including its original field path and combined budget. The
function branch enters its smaller body directly. This links binder focusing
to the existing first-root theorem, without assuming a new execution. -/
theorem PiInertPairWeightedBodyRoot.binder_descent
    (H : PiInertPairWeightedBodyRoot D Δ family info original u out budget stage (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) fields) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) :
    (∃ B innerU smaller, smaller < budget ∧
      PiInertProjectionContinuationMinimum D Δ family 0 out (B :: A :: Δ)
        (.app ((ProofShape.mkApps (.const info.ctorName []) fields).liftN 1) (etaArgument innerU)) smaller) ∨
    (∃ short later charge smaller, charge+smaller < budget ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D later) charge Δ original short ∧
      fields = [short.liftN 1, etaArgument u] ∧
      PiInertProjectionContinuationMinimum D Δ family 0 out (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [short.liftN 1, etaArgument u]) smaller ∧
      PiInertBinderExitMinimum D Δ family out A
        (ProofShape.mkApps (.const info.ctorName []) [short.liftN 1, etaArgument u]) smaller) := by
  rcases H.observed_descent heq hs with HF | ⟨short, levels, later, charge, smaller, hc, HT, RF, ES, HM⟩
  · exact .inl HF
  · obtain ⟨_, EL, EFields⟩ := ProofShape.const_spine_inj ES
    cases EL
    have HM' : PiInertProjectionContinuationMinimum D Δ family 0 out (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [short.liftN 1, etaArgument u]) smaller :=
      EFields ▸ HM
    exact .inr ⟨short, later, charge, smaller, hc, HT, RF, EFields, HM',
      HM'.pair_binder_exit heq hs hi hp hz (by simp [hf])⟩

end Lean4Lean.VEnv.Strengthening
