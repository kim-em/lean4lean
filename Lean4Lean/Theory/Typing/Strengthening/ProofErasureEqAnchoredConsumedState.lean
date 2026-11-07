import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAnchoredRecognitionState

/-! # Consumed-frame returns in the exact recognition state

Restore actual supplies at every returned depth, including depth zero. The
source application witness supplies dependent typing; the endpoint's agreeing
realization supplies exact raw syntax. The global recognizer remains unproved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private typed_lambda_readout typed_lambda_argument_map lambda_body_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
variable [Params]

/-- Restore arbitrary raw upper arguments to a completed recognition state.
A positive history attaches them to its outer wrapper; at depth zero they join
the leaf's upper extras. Neither case changes depth or invents lower arguments. -/
theorem EqAnchoredEndpoint.append_extra
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ [] v w original endpoint depth)
    (tail : List ProofShape) :
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ [] v w original (ProofShape.mkApps endpoint tail) depth := by
  by_cases hz : depth = 0
  · subst depth
    obtain ⟨v', w', pre, extra, F, HP, hf, hn, _, rfl⟩ := H.zero_depth_spine
    simpa only [← ProofShape.mkApps_append, List.append_assoc] using
      (EqAnchoredEndpoint.of_spine (D := D) (Λ := Λ₀) (blocks := blocks₀) HP hf hn
        (extra := extra ++ tail) (.inr rfl))
  · obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
      HH, HP, hf, hn, hxtra, rfl⟩ := H
    obtain ⟨returned, HR, EW⟩ := HH.append_outer_extra tail (by omega)
    exact ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, returned, chosen,
      HR, HP, hf, hn, hxtra, (EW _).symm⟩

/-- Restore a typed waiting supply at any recognized depth. At positive depth
all source anchors are retained by outer supply restoration. At depth zero,
recognition supplies the actual chosen spine; its equality with the returned
function transfers whole application typing before appending chosen arguments.
Untracked old extras force an empty new tracked vector. -/
theorem EqAnchoredEndpoint.append_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ (supplied ++ pending₀) v w original endpoint depth)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps f actual) T)
    (hn : ¬ IsProof Γ₀ (VExpr.mkApps f actual))
    (RF : ScopedCompute Step (proofEraseCtx Λ₀) (blocks₀.erased (proofErase Γ₀ f)) endpoint) :
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w original
      (ProofShape.mkApps endpoint (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra)) depth := by
  by_cases hz : depth = 0
  · subst depth
    obtain ⟨v', w', pre, oldExtra, F, HP, hf, hnf, hxtra, rfl⟩ := H.zero_depth_spine
    rcases hxtra with rfl | hnil
    · obtain ⟨Tf, hfun⟩ := VExpr.WF.of_mkApps henv.orderedStrong W.actual.wf ⟨_, happ⟩
      have RF' : ScopedCompute Step (proofEraseCtx Λ₀) (blocks₀.erased (proofErase Γ₀ f))
          (blocks₀.erased (proofErase Γ₀ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))) := by
        simpa only [proofErase_const_spine W.actual.wf hf hnf, EqInsertionPath.erased_const_spine,
          List.append_nil] using RF
      have HE := J.compute_recognized_endpoint hstep W hfun hf hnf RF'
      obtain ⟨HP', HEwhole, hnwhole⟩ := HP.restore_computed_supply hΔ HS HE.toU
        (List.Forall₂.rfl HS.1) happ hn
      simpa only [List.map_append, ← ProofShape.mkApps_append, List.append_assoc, List.append_nil] using
        (EqAnchoredEndpoint.of_spine (D := D) (Λ := Λ₀) (blocks := blocks₀) HP' HEwhole.hasType.2 hnwhole hextra)
    · obtain ⟨hsup, hpend⟩ := List.append_eq_nil_iff.mp hnil
      subst supplied
      subst pending₀
      have hactual : actual = [] := by
        have HL := HS.2.length_eq
        simp only [List.length_nil, List.length_map] at HL
        exact List.length_eq_zero_iff.mp HL.symm
      subst actual
      simpa only [List.map_nil, List.nil_append, ← ProofShape.mkApps_append, List.append_assoc] using
        (EqAnchoredEndpoint.of_spine (D := D) (Λ := Λ₀) (blocks := blocks₀) HP hf hnf
          (extra := oldExtra ++ extra) (.inr rfl))
  · obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, localExtra, F, plug, chosen,
      HH, HP, hf, hnf, hxtra, rfl⟩ := H
    obtain ⟨returned, HR, EW⟩ := HH.append_outer_supply heq hs hstep W J rfl HS hextra happ hn RF (by omega)
    exact ⟨Γ, Λ, σ, blocks, pending, v', w', pre, localExtra, F, returned, chosen,
      HR, HP, hf, hnf, hxtra, (EW _).symm⟩

/-- Consume an actual unused upper binder from a recognized body and restore
its raw waiting tail at any returned depth. Actual interpretation determines
the upper square; the lower chosen assignment stays fixed. -/
theorem EqAnchoredEndpoint.consume_unused
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ ω blocks)
    (hA : env.HasType univs Λ A (.sort u))
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX))
    (H : EqAnchoredEndpoint D Δ Γ (A :: Λ) σ (blocks ++ [(1,0)]) [] v w original body depth)
    (rawRest : List ProofShape) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks [] v w original
      (ProofShape.mkApps (body.inst rawX) rawRest) depth := by
  obtain ⟨x, _, _, Q⟩ := EqSupplyInsertionSquare.unused_argument hΔ W J hA WX
  have HR := (H.realize heq hs hΔ Q).append_extra rawRest
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR

/-- Consume a chosen source anchor whose body has been recognized. Whole
application typing comes from the stored source application and its actual body
path; the recognized state is realized through the chosen argument square.
Restoring the tail handles both zero and positive returned depths, without a
native computation under substituted syntax or a new application-typing premise. -/
theorem EqRetainedSourceAnchor.consume_recognized
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ ω blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body (rawX :: rawRest))
    (HB : EqAnchoredEndpoint D Δ (A :: Γ) (blocks.actual A :: Λ) (σ.cons y)
      blocks.underBinder remaining v w original body depth) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original
      (ProofShape.mkApps (body.inst rawX) rawRest) depth := by
  obtain ⟨hΓ, e, T, supplied, actual, extra, F, n, he, happ, hn, HS, EP, hextra, ER, RB⟩ := H
  cases actual with
  | nil =>
    cases HS.2
    rcases hextra with rfl | rfl
    · cases ER
    · cases EP
  | cons x actual =>
    obtain ⟨HT, HE⟩ := HS
    cases HE with
    | cons HY HTail =>
      obtain ⟨EY, Etail⟩ := List.cons.inj EP
      cases EY
      obtain ⟨EX, Erest⟩ := List.cons.inj ER
      have Hhead : VExpr.WF env univs Γ (.app (.lam A e) x) :=
        VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, happ⟩
      have hx := HasType.app_lam_arg hΓ Hhead.choose_spec
      have HY := HY.of_r henv hΔ (hx.subst henv.orderedStrong W.agree.left hΔ)
      have Htail : EqArgumentSupplyAt Γ Δ σ _ actual :=
        ⟨fun z hz => HT z (List.mem_cons_of_mem x hz), HTail⟩
      have Q := EqSupplyInsertionSquare.of_chosen_argument hΔ W J hA hx HY
      rw [EX] at Q
      obtain ⟨f, HF, Hwhole, hnwhole, hnf, EF⟩ := Q.compute_consumed_application
        (pi_inert_stage_certificate_descent heq hs n) hΔ hA he hx RB
        (List.Forall₂.rfl Htail.1) happ hn
      have HR := HB.realize heq hs hΔ Q
      have HR : EqAnchoredEndpoint D Δ Γ Λ σ blocks remaining v w original (body.inst rawX) depth := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR
      rw [← Etail] at HR
      have RF : ScopedCompute (PiInertStage D 0) (proofEraseCtx Λ)
          (blocks.erased (proofErase Γ f)) (body.inst rawX) := EF ▸ .refl
      have HR := HR.append_supply heq hs (pi_inert_stage_certificate_descent heq hs 0)
        hΔ W J Htail hextra Hwhole.hasType.2 hnwhole RF
      rw [← Erest]
      exact HR

/-- Actual body and argument computations update the chosen source anchor and
produce the recognized input to the consumed suffix. The supplied body induction
bound proves both recursive decreases for the lexicographic order on primitive
cost and incoming depth. This does not yet recognize the suffix itself. -/
theorem EqRetainedSourceAnchor.consumed_recognition
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ ω blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args)
    (RB : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ)) body body')
    (RA : ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args (rawX :: rawRest))
    (HB : EqAnchoredEndpoint D Δ (A :: Γ) (blocks.actual A :: Λ) (σ.cons y)
      blocks.underBinder remaining v w original body' returnedDepth)
    (hdepth : returnedDepth ≤ incomingDepth+cb) (hcost : cd+cb+ca+cs ≤ cost) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original
      (ProofShape.mkApps (body'.inst rawX) rawRest) returnedDepth ∧
    (cb < cost ∨ cb = cost ∧ incomingDepth < incomingDepth+1) ∧
    (cs < cost ∨ cs = cost ∧ returnedDepth < incomingDepth+1) := by
  have HA := H.compute_arguments (pi_inert_stage_certificate_descent heq hs n) hΔ W J RA.forget
  have HA' := HA.compute_body RB.forget
  exact ⟨HA'.consume_recognized heq hs hΔ W J hA HB,
    pending_history_readout_decreases hcost hdepth⟩

/-- Read an existing lambda state with the exact typed continuations and
unrestricted minima required by recursive recognition. Unlike a fresh eta cut,
entering this body need not lower primitive cost; the separate incoming-depth
measure handles equality. Consumption also derives the suffix minimum from
its actual fixed body path. No native computation is substituted. -/
theorem pi_inert_lambda_recognition_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps (.lam A body) args) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A body) args) tail → K tail k → cost+ck ≤ j+k) :
    TypedSource (A :: Δ) body ∧ (
      (∃ A' body' args' u cd cb ca m,
        DomainSort Δ A u ∧ cd+cb+ca = cost ∧
        endpoint = ProofShape.mkApps (.lam A' body') args' ∧
        ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
        ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) Δ ca args args' ∧
        PiInertTypedContinuationRun D Ω out (A :: Δ)
          (fun b k => K (ProofShape.mkApps (.lam A' b) args') k) body' ck ∧
        ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) body tail →
          K (ProofShape.mkApps (.lam A' tail) args') k → cb+ck ≤ j+k) ∨
      (∃ A' body' x' xs' u cd cb ca cs m,
        DomainSort Δ A u ∧ cd+cb+ca+cs = cost ∧
        ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
        ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
        ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
        TypedSource Δ (ProofShape.mkApps (body'.inst x') xs') ∧
        ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') endpoint ∧
        PiInertTypedContinuationRun D Ω out (A :: Δ)
          (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K) body' (cs+ck) ∧
        (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) body tail →
          PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K tail k → cb+(cs+ck) ≤ j+k) ∧
        ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
          (ProofShape.mkApps (body'.inst x') xs') tail → K tail k → cs+ck ≤ j+k)) := by
  have HTlam : TypedSource Δ (.lam A body) := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody A .hole).typed HTlam
  refine ⟨HTbody, ?_⟩
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', body', args', cf, ca, hc, rfl, RF, RX⟩ |
    ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨u, cd, cb, m, SD, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have hexact := HM _ _ _ ck (lambda_body_replace RD RB RX) HK.holds
    refine .inl ⟨A', body', args', u, cd, cb, ca, m, SD, by omega, rfl, RD, RB, RX, ?_, ?_⟩
    · exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HK
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
    have hexact := HM _ _ _ ck Ractual HK.holds
    have HBmin : ∀ later j tail k,
        ScopedComputeCount (PiInertStage D later) j (A :: Δ) body tail →
        PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K tail k →
        cb+(cs+ck) ≤ j+k := by
      rintro later j tail k RJ ⟨suffixStage, tailCount, last, lastCost, hsum, RT, HL⟩
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
    refine .inr ⟨A', body', x', xs', u, cd, cb, ca, cs, m, SD, by omega,
      RD, RB, RX, WI, HTnext, RS, ?_, HBmin, ?_⟩
    · exact .application (HTbody.pi_inert_compute heq hs RB.forget) (.inst WI)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext)
        (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) HK
    · intro later j tail k RJ HL
      have HB := HBmin m cb body' (j+k) RB ⟨later, j, tail, k, rfl,
        by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ, HL⟩
      omega

end Lean4Lean.VEnv.Strengthening
