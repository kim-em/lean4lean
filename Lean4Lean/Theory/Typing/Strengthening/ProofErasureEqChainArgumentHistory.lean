import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainRetainedSupply

/-! # Keep the chosen images of actual continuation arguments

An argument vector can wait outside the currently tracked Eq spine. Its
chosen target images must survive actual computation and agreeing scope moves
until the vector supplies a binder. These records concern actual typed terms;
they impose no substitution closure on guarded computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private args_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixSpecialization
variable [Params]

/-- Chosen target images attached to an actual, individually typed argument
vector. The arguments need not currently be applied to the tracked Eq head.
The chosen substitution's typing is supplied by the concrete paired frame. -/
def EqArgumentSupplyAt (Γ Δ : List VExpr) (σ : VExpr.Subst)
    (chosen actual : List VExpr) : Prop :=
  (∀ e ∈ actual, VExpr.WF env univs Γ e) ∧
    List.Forall₂ (env.IsDefEqU univs Δ) chosen (actual.map (·.subst σ))

/-- Initialize from actual typed arguments before they enter a continuation. -/
theorem EqArgumentSupplyAt.of_typed
    (hΔ : OnCtx Δ (env.IsType univs)) (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (H : ∀ e ∈ actual, VExpr.WF env univs Γ e) :
    EqArgumentSupplyAt Γ Δ σ (actual.map (·.subst σ)) actual := by
  refine ⟨H, List.Forall₂.rfl ?_⟩
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
  obtain ⟨T, ht⟩ := H a ha
  exact ⟨_, ht.subst henv.orderedStrong W hΔ⟩

/-- An agreeing actual scope move preserves the same chosen images. The raw
argument vector is exactly the endpoint substitution of the old vector. -/
theorem EqArgumentSupplyAt.frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ chosen actual)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ) :
    EqArgumentSupplyAt Γ' Δ σ' chosen (actual.map (·.subst ρ)) ∧
      (actual.map (·.subst ρ)).map (proofErase Γ') = (actual.map (proofErase Γ)).map (·.subst τ) := by
  have HR : List.Forall₂ (env.IsDefEqU univs Δ) (actual.map (·.subst σ))
      ((actual.map (·.subst ρ)).map (·.subst σ')) := by
    apply List.forall₂_of_getElem (by simp only [List.length_map])
    intro i hi hi'
    have hia : i < actual.length := by simpa only [List.length_map] using hi
    obtain ⟨T, ht⟩ := H.1 actual[i] (List.getElem_mem hia)
    simpa only [List.getElem_map] using (W.term hΔ ht).toU
  refine ⟨⟨?_, H.2.trans (fun _ _ _ h k => h.trans henv hΔ k) HR⟩, ?_⟩
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    obtain ⟨T, ht⟩ := H.1 a ha
    exact ⟨_, ht.subst henv.orderedStrong W.actual W.target.wf⟩
  · simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨T, ht⟩ := H.1 e he
    exact proofErase_subst_with W.target.wf W.actual ht W.erase

/-- Reify actual argument computation through the full insertion chain.
Both the original chosen images and pointwise source equalities are kept,
including for arguments waiting outside the currently tracked prefix. -/
theorem EqArgumentSupplyAt.chain_compute
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ chosen actual)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((actual.map (proofErase Γ)).map blocks.erased) raw) :
    ∃ actual', EqArgumentSupplyAt Γ Δ σ chosen actual' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) actual actual' ∧
      ((actual'.map (proofErase Γ)).map blocks.erased) = raw := by
  have realize : ∀ (args : List VExpr) raw,
      (∀ e ∈ args, VExpr.WF env univs Γ e) →
      List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
        ((args.map (proofErase Γ)).map blocks.erased) raw →
      ∃ args', (∀ e ∈ args', VExpr.WF env univs Γ e) ∧
        List.Forall₂ (env.IsDefEqU univs Γ) args args' ∧
        ((args'.map (proofErase Γ)).map blocks.erased) = raw := by
    intro args
    induction args with
    | nil => intro raw _ RA; cases RA; exact ⟨[], by simp, .nil, rfl⟩
    | cons a args ih =>
      intro raw HT RA
      cases RA with
      | cons R RA =>
        obtain ⟨T, ht⟩ := HT a (by simp)
        obtain ⟨a', HE, _, EE⟩ := J.compute_certificate hstep W ht R
        obtain ⟨args', HT', HR, ER⟩ := ih _ (fun e he => HT e (by simp [he])) RA
        refine ⟨a' :: args', ?_, .cons HE.toU HR, ?_⟩
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨T, HE.hasType.2⟩
          · exact HT' e he
        · simp only [List.map_cons, EE, ER]
  obtain ⟨actual', HT', HE, EE⟩ := realize actual raw H.1 RA
  exact ⟨actual', ⟨HT', H.2.trans (fun _ _ _ h k => h.trans henv hΔ k)
    (args_subst hΔ W.agree.left HE)⟩, HE, EE⟩

/-- Computation followed by the actual agreeing frame retains chosen images
and the precise outgoing upper raw vector. No guarded path is substituted. -/
theorem EqArgumentSupplyAt.chain_compute_frame
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ chosen actual)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((actual.map (proofErase Γ)).map blocks.erased) raw) :
    ∃ actual', EqArgumentSupplyAt Γ Δ σ chosen actual' ∧
      EqArgumentSupplyAt Γ' Δ σ' chosen (actual'.map (·.subst ρ)) ∧
      ((actual'.map (proofErase Γ)).map blocks.erased) = raw ∧
      (((actual'.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) = raw.map (·.subst υ) := by
  obtain ⟨actual', HS, _, EE⟩ := H.chain_compute hstep hΔ W J RA
  obtain ⟨HS', ES⟩ := HS.frame hΔ W
  refine ⟨actual', HS, HS', EE, ?_⟩
  rw [ES, ← EE]
  simp only [List.map_map, Function.comp_def, J.erased]

/-- Opening a newer chosen binder preserves waiting older arguments and their
images. Their actual representatives lift; their chosen images stay fixed. -/
theorem EqArgumentSupplyAt.under_binder
    (H : EqArgumentSupplyAt Γ Δ σ chosen actual) :
    EqArgumentSupplyAt (A :: Γ) Δ (σ.cons y) chosen (actual.map VExpr.lift) := by
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    obtain ⟨T, ht⟩ := H.1 a ha
    exact ⟨T.lift, ht.weak henv⟩
  · simpa only [List.map_map, Function.comp_def, VExpr.lift_subst_cons] using H.2

/-- The recorded head image gives the consumption frame at its actual displayed
domain. The rest of the vector retains its own chosen images for later supply. -/
theorem EqArgumentSupplyAt.consume_head
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ (y :: chosen) (x :: actual))
    (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A) :
    EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons y) σ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) ∧ EqArgumentSupplyAt Γ Δ σ chosen actual := by
  cases H.2 with
  | cons HY HR =>
    exact ⟨EqSpecializationFrame.inst W hA hx
      (HY.of_r henv hΔ (hx.subst henv.orderedStrong W hΔ)),
      ⟨fun e he => H.1 e (List.mem_cons_of_mem x he), HR⟩⟩

/-- Taking an actual Eq prefix initializes the waiting supply with exactly
the images moved into that prefix's pending vector. -/
theorem EqPrefixSpecializationAt.pending_argument_supply
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F) (arity : Nat) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.take arity) σ
      ((pre.drop arity).map (·.subst σ) ++ pending) ∧
    EqArgumentSupplyAt Γ Δ σ ((pre.drop arity).map (·.subst σ)) (pre.drop arity) := by
  refine ⟨H.take arity, EqArgumentSupplyAt.of_typed hΔ H.1 ?_⟩
  intro e he
  exact (mkApps_arguments_wf henv H.1.wf ⟨_, ht⟩).2 e (List.mem_of_mem_drop he)

/-- Compute the tracked supply prefix while keeping arbitrary additional
upper arguments and their actual paths. Such extras need no lower realization
or chosen target image, including the original probe's erased major proof. -/
theorem EqArgumentSupplyAt.chain_compute_prefix
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ chosen actual)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      (((actual.map (proofErase Γ)).map blocks.erased) ++ extra) raw) :
    ∃ actual' rawExtra, EqArgumentSupplyAt Γ Δ σ chosen actual' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) actual actual' ∧
      ((actual'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = raw ∧
      List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) extra rawExtra := by
  have RP := Lean4Lean.List.forall₂_take RA ((actual.map (proofErase Γ)).map blocks.erased).length
  simp only [List.take_left] at RP
  simp only [List.length_map] at RP
  have RX := Lean4Lean.List.forall₂_drop RA ((actual.map (proofErase Γ)).map blocks.erased).length
  simp only [List.drop_left] at RX
  simp only [List.length_map] at RX
  obtain ⟨actual', HS, HE, EE⟩ := H.chain_compute hstep hΔ W J RP
  exact ⟨actual', raw.drop actual.length, HS, HE, by rw [EE, List.take_append_drop], RX⟩

/-- The actual computed vector determines its consumed head and remaining
supply. The head's chosen-image agreement is recovered from the stored history,
and its displayed-domain typing follows from the source argument equality.
The tail's source equalities are retained separately from its chosen images. -/
theorem EqArgumentSupplyAt.chain_consumed_head
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ (y :: chosen) (x :: actual))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((((x :: actual).map (proofErase Γ)).map blocks.erased) ++ extra) (rawX :: rawRest)) :
    ∃ x' rest' rawExtra, env.IsDefEq univs Γ x x' A ∧
      blocks.erased (proofErase Γ x') = rawX ∧
      ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest ∧
      List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) extra rawExtra ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons y) σ (VExpr.Subst.one x')
        (ProofShape.Subst.one (proofErase Γ x')) ∧ EqArgumentSupplyAt Γ Δ σ chosen rest' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) actual rest' := by
  obtain ⟨args', rawExtra, HS, HE, EE, RX⟩ := H.chain_compute_prefix hstep hΔ W J RA
  cases args' with
  | nil => cases HE
  | cons x' rest' =>
    obtain ⟨EX, ER⟩ := List.cons.inj EE
    cases HE with
    | cons HX Hrest =>
      have HX := HX.of_l henv W.actual.wf hx
      obtain ⟨WF, HR⟩ := HS.consume_head hΔ W.agree.left hA HX.hasType.2
      exact ⟨x', rest', rawExtra, HX, EX, ER, RX, WF, HR, Hrest⟩

/-- The two exact continuation branches created by actual eta execution,
with chosen images still attached to every supplied argument. The consumed
branch includes a derived matching frame, while the retained branch keeps
the entire vector available. Both branches preserve their original competitor
predicate and source argument equalities; this is not a claim of arbitrary continuation closure. -/
def EqSuppliedEtaContinuation (D : Definitions) (n : Nat) (Γ Δ Λ : List VExpr)
    (σ : VExpr.Subst) (blocks : EqInsertionPath) (A x y : VExpr) (chosen actual : List VExpr)
    (f : ProofShape) (u : VLevel) (Ω : List ProofShape) (out endpoint : ProofShape)
    (ck cost : Nat) (extra : List ProofShape) (K : ProofShape → Nat → Prop) : Prop :=
    (∃ A' body' args' raw rawExtra cd cb m,
      EqArgumentSupplyAt Γ Δ σ (y :: chosen) args' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) (x :: actual) args' ∧
      ((args'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = raw ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra rawExtra ∧
      endpoint = ProofShape.mkApps (.lam A' body') raw ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (proofErase Λ (blocks.actual A)) A' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (fun body k => K (ProofShape.mkApps (.lam A' body) raw) k) body' ck ∧ cb+ck < cost ∧
      ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) body →
        K (ProofShape.mkApps (.lam A' body) raw) k → cb+ck ≤ j+k) ∨
    (∃ x' rest' rawX rawRest rawExtra body' cb cs m,
      env.IsDefEq univs Γ x x' A ∧ blocks.erased (proofErase Γ x') = rawX ∧
      ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra rawExtra ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons y) σ (VExpr.Subst.one x')
        (ProofShape.Subst.one (proofErase Γ x')) ∧ EqArgumentSupplyAt Γ Δ σ chosen rest' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) actual rest' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
        (ProofShape.mkApps (body'.inst rawX) rawRest) endpoint ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K)
        body' (cs+ck) ∧ cb+(cs+ck) < cost ∧
      ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) body →
        PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K body k →
        cb+(cs+ck) ≤ j+k)

/-- Read the actual eta execution with its argument history intact. In the
retained branch the whole computed vector keeps its chosen images. In the
consumed branch the actual vector computation derives the chosen consumption
frame and leaves the tail's images attached to its exact raw arguments. Both
branches retain the specific induced continuation and unrestricted body
minimum, so further nested cuts can use this history. Global preservation
through every subsequent continuation still has to be established. -/
theorem CountedEtaFrameOrigin.argument_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HS : EqArgumentSupplyAt Γ Δ σ (y :: chosen) (x :: actual))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (H : CountedEtaFrameOrigin D n (proofEraseCtx Λ) f (proofErase Λ (blocks.actual A)) u
      ((((x :: actual).map (proofErase Γ)).map blocks.erased) ++ extra) endpoint ct ck cost K)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck) :
    EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x y chosen actual f u Ω out endpoint ck cost extra K := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', raw, cf, ca, cd, cb, m, _, _, EO, _, RA, RD, HT, RB, hsmall, HM⟩ |
    ⟨A', body', rawX, rawRest, cf, ca, cs, cd, cb, m, _, _, _, RA, _, HT, RB, WI, HTnext, RS, hsmall, HM⟩
  · obtain ⟨args', rawExtra, HS', Hargs, ER, RX⟩ := HS.chain_compute_prefix (pi_inert_stage_certificate_descent heq hs n) hΔ W J RA.forget
    have HK' : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K
        (ProofShape.mkApps (.lam A' body') raw) ck := EO ▸ HK
    have HR := PiInertTypedContinuationRun.retained (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HK'
    exact .inl ⟨A', body', args', raw, rawExtra, cd, cb, m, HS', Hargs, ER, RX, EO, RD, HT, RB, HR, hsmall, HM⟩
  · obtain ⟨x', rest', rawExtra, HX, EX, ER, RX, WF, HS', Hargs⟩ := HS.chain_consumed_head
      (pi_inert_stage_certificate_descent heq hs n) hΔ W J hA hx RA.forget
    have RT : ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one rawX)) rawRest) endpoint := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource (proofEraseCtx Λ)
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one rawX)) rawRest) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    have HR := PiInertTypedContinuationRun.application (HT.pi_inert_compute heq hs RB.forget)
      (.inst WI) HTnext' RT HK
    refine .inr ⟨x', rest', rawX, rawRest, rawExtra, body', cb, cs, m,
      HX, EX, ER, RX, WF, HS', Hargs, HT, RB, RS, HR, by omega, ?_⟩
    intro later j body k RJ HL
    have HH := HM later j body k RJ HL
    omega

/-- The history-enriched branches retain the original strictly smaller typed
minimum at the same fresh body. The argument history remains available in the
input record; forgetting it here does not alter the chosen continuation. -/
theorem EqSuppliedEtaContinuation.minimum
    (H : EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x y chosen actual f u Ω out endpoint ck cost extra K) :
    ∃ smaller, smaller < cost ∧ PiInertTypedContinuationMinimum D Ω out
      (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) smaller := by
  rcases H with
    ⟨A', body', args', raw, rawExtra, cd, cb, m, _, _, _, _, _, _, HT, RB, HR, hsmall, HM⟩ |
    ⟨x', rest', rawX, rawRest, rawExtra, body', cb, cs, m, _, _, _, _, _, _, _, HT, RB, _, HR, hsmall, HM⟩
  · exact ⟨cb+ck, hsmall, _, m, cb, ck, body', HT, RB, HR, rfl, HM⟩
  · exact ⟨cb+(cs+ck), hsmall, _, m, cb, cs+ck, body', HT, RB, HR, rfl, HM⟩

/-- Construct the supplied continuation history directly from the actual
parent eta path and its fixed outer continuation. The argument history at
entry may be initialized by `pending_argument_supply`; the selected suffix
itself supplies every subsequent raw argument computation and consumption
map. No later argument-image agreement is assumed separately. -/
theorem pi_inert_eta_chain_argument_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HS : EqArgumentSupplyAt Γ Δ σ (y :: chosen) (x :: actual))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (HT : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps f ((((x :: actual).map (proofErase Γ)).map blocks.erased) ++ extra)))
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ) f
      (.forallE (proofErase Λ (blocks.actual A)) rawB))
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps f ((((x :: actual).map (proofErase Γ)).map blocks.erased) ++ extra)))
    (HR : PiInertStage D n (proofEraseCtx Λ) f
      (.lam (proofErase Λ (blocks.actual A)) (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam (proofErase Λ (blocks.actual A))
        (.app (f.liftN 1) (etaArgument u)))
        ((((x :: actual).map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x y chosen actual f u Ω out endpoint ck cost extra K := by
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have SD : DomainSort (proofEraseCtx Λ) (proofErase Λ (blocks.actual A)) u :=
    ⟨Λ, blocks.actual A, (J.actual W).2.1.wf, rfl, hAup, rfl⟩
  exact (pi_inert_eta_frame_origin heq hs hguard HT RN SD RP HR RT HK.holds hcost HM).argument_history
    heq hs hΔ HS W J hA hx HK

end Lean4Lean.VEnv.Strengthening
