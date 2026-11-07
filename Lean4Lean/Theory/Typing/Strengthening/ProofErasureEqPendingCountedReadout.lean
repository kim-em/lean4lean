import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingSupplyRestore

/-! # Read actual retained computations with their pending supplies

Read the exact counted lambda body and argument paths before any continuation
minimum is chosen. A consumed local head is identified even when enclosing
chosen arguments remain pending. The remaining supply and enclosing tail are
kept distinct for recursive return.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
private theorem actual_id_liftN (n : Nat) : VExpr.Subst.id.liftN n = VExpr.Subst.id := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [VExpr.Subst.liftN, ih, VExpr.id_lift]

private theorem raw_id_liftN (n : Nat) : ProofShape.Subst.id.liftN n = ProofShape.Subst.id := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ProofShape.Subst.liftN, ih, ProofShape.Subst.id_lift]

variable [Params]

/-- An actually nonempty retained vector has a lower chosen head, even when
enclosing arguments remain pending. If the lower local supply were empty,
nonempty extras would force empty enclosing pending and contradict the binder's
chosen-image equation. The remaining local images are separated from that tail. -/
theorem EqRetainedArgumentSupply.nonempty_head
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining (rawX :: rawRest))
    (S : Ctx.SubstEq env univs Δ σ σ Γ) :
    ∃ x supplied actual extra,
      env.HasType univs Γ x A ∧ env.IsDefEq univs Δ y (x.subst σ) (A.subst σ) ∧
      remaining = supplied ++ pending ∧ EqArgumentSupplyAt Γ Δ σ supplied actual ∧
      blocks.erased (proofErase Γ x) = rawX ∧
      ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = rawRest ∧
      (extra = [] ∨ pending = []) := by
  obtain ⟨supplied, actual, extra, HS, hx, EP, hextra, ER⟩ := H
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
      have hx := hx x actual rfl
      obtain ⟨EX, ET⟩ := List.cons.inj ER
      exact ⟨x, _, actual, extra, hx, HY.of_r henv hΔ
        (hx.subst henv.orderedStrong S hΔ), Etail.symm,
        ⟨fun e he => HT e (List.mem_cons_of_mem x he), HTail⟩, EX, ET, hextra⟩

/-- Further actual argument computation derives the exact chosen consumption
square and splits the residual pending vector into the waiting local supply
and enclosing pending tail. No assumption that the enclosing tail is empty is
needed, and the displayed raw head is the square's literal substitution image. -/
theorem EqRetainedArgumentSupply.compute_consume
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining raw)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) raw (rawX :: rawRest)) :
    ∃ x supplied actual extra,
      env.HasType univs Γ x A ∧ remaining = supplied ++ pending ∧
      EqArgumentSupplyAt Γ Δ σ supplied actual ∧
      blocks.erased (proofErase Γ x) = rawX ∧
      ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = rawRest ∧
      (extra = [] ∨ pending = []) ∧
      EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
        (VExpr.Subst.one x) (ProofShape.Subst.one (proofErase Γ x))
        (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x))
        (ProofShape.Subst.one rawX) blocks.underBinder blocks := by
  have H' := H.chain_compute hstep hΔ W J RA
  obtain ⟨x, supplied, actual, extra, hx, HY, EP, HS, EX, ER, hextra⟩ :=
    H'.nonempty_head hΔ W.agree.left
  exact ⟨x, supplied, actual, extra, hx, EP, HS, EX, ER, hextra,
    by simpa only [EX] using EqSupplyInsertionSquare.of_chosen_argument hΔ W J hA hx HY⟩

/-- Read an actual chosen retained lambda-spine computation without a minimum
premise. Both branches keep the original body scope and exact primitive-cost
split. The consumed branch derives its square and remaining chosen supply from
the actual argument path, even with a nonempty enclosing pending vector. -/
theorem EqRetainedArgumentSupply.counted_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining args)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (HT : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam (blocks.erased (proofErase Γ A)) body) args))
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam (blocks.erased (proofErase Γ A)) body) args) endpoint) :
    TypedSource (proofEraseCtx (blocks.actual A :: Λ)) body ∧ (
      (∃ rawA' body' args' cd cb ca m,
        cd+cb+ca ≤ cost ∧ endpoint = ProofShape.mkApps (.lam rawA' body') args' ∧
        ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
          (blocks.erased (proofErase Γ A)) rawA' ∧
        ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ)) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args args' ∧
        EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining args') ∨
      (∃ x supplied actual extra rawX rawRest rawA' body' cd cb ca cs m,
        cd+cb+ca+cs ≤ cost ∧ env.HasType univs Γ x A ∧ remaining = supplied ++ pending ∧
        EqArgumentSupplyAt Γ Δ σ supplied actual ∧
        blocks.erased (proofErase Γ x) = rawX ∧
        ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = rawRest ∧
        (extra = [] ∨ pending = []) ∧
        EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
          (VExpr.Subst.one x) (ProofShape.Subst.one (proofErase Γ x))
          (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x))
          (ProofShape.Subst.one rawX) blocks.underBinder blocks ∧
        ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
          (blocks.erased (proofErase Γ A)) rawA' ∧
        ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ)) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args (rawX :: rawRest) ∧
        TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (body'.inst rawX) rawRest) ∧
        ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
          (ProofShape.mkApps (body'.inst rawX) rawRest) endpoint)) := by
  have Ectx : proofEraseCtx (blocks.actual A :: Λ) =
      blocks.erased (proofErase Γ A) :: proofEraseCtx Λ := by
    rw [proofEraseCtx, J.erase_actual W hA]
  have HTlam := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody (blocks.erased (proofErase Γ A)) .hole).typed HTlam
  refine ⟨by simpa only [Ectx] using HTbody, ?_⟩
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨rawA', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨rawA', body', rawX, rawRest, cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨v, cd, cb, m, _, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    exact .inl ⟨rawA', body', args', cd, cb, ca, m, by omega, EO, RD,
      by simpa only [Ectx] using RB, RX,
      H.chain_compute (pi_inert_stage_certificate_descent heq hs n) hΔ W J RX.forget⟩
  · obtain ⟨v, cd, cb, m, _, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    obtain ⟨x, supplied, actual, extra, hx, EP, HS, EX, ER, hextra, Q⟩ :=
      H.compute_consume (pi_inert_stage_certificate_descent heq hs n) hΔ W J hA RX.forget
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 (proofEraseCtx Λ)
        (ProofShape.mkApps (.lam rawA' body') (rawX :: rawRest))
        (ProofShape.mkApps (body'.inst rawX) rawRest) := by
      simpa only [ProofShape.mkApps] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := rawA') (b := body') (a := rawX))).mkApps
          (ScopedArgumentsCount.refl (args := rawRest))
    have HTnext := HT.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
    exact .inr ⟨x, supplied, actual, extra, rawX, rawRest, rawA', body', cd, cb, ca, cs, m,
      by omega, hx, EP, HS, EX, ER, hextra, Q, RD, by simpa only [Ectx] using RB,
      RX, HTnext, RS⟩

omit [Params] in
/-- The exact readout budget supports the proposed lexicographic recursive
calls. A body call loses one incoming wrapper. A subsequent suffix call also
loses one at equal primitive cost, provided recursive body recognition proves
its output-depth bound. That bound is an explicit premise, not proved here. -/
theorem pending_history_readout_decreases
    (hcost : cd+cb+ca+cs ≤ cost) (hdepth : returnedDepth ≤ depth+cb) :
    (cb < cost ∨ cb = cost ∧ depth < depth+1) ∧
    (cs < cost ∨ cs = cost ∧ returnedDepth < depth+1) := by
  omega

/-- Expose the actual outermost retained frame and its inner pending history.
The split retains source domains, native annotation paths, chosen-image supply,
raw wrapper composition and exact binder counts. An unused outer frame has an
empty base pending vector. This is the structural split needed before reading
an arbitrary native suffix of the whole wrapper. -/
theorem EqPendingSupplyHistory.outermost
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (hd : 0 < depth) :
    (∃ A u y rawA args remaining n cd inner chosen' depth',
      env.HasType univs Γ₀ A (.sort u) ∧ env.HasType univs Δ y (A.subst σ₀) ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀)
        (blocks₀.erased (proofErase Γ₀ A)) rawA ∧
      EqRetainedArgumentSupply Γ₀ Δ σ₀ blocks₀ A y pending₀ remaining args ∧
      EqPendingSupplyHistory D Δ (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y)
        blocks₀.underBinder remaining (rawA.subst υ₀ :: Ψ₀) υ₀.lift
        Γ Λ σ blocks pending Ψ υ inner chosen' depth' ∧
      chosen = chosen'+1 ∧ depth = depth'+1 ∧
      ∀ e, plug e = ProofShape.mkApps (.lam rawA (inner e)) args) ∨
    (∃ A u rawA args n cd inner depth', pending₀ = [] ∧
      env.HasType univs Λ₀ A (.sort u) ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀) (proofErase Λ₀ A) rawA ∧
      EqPendingSupplyHistory D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
        (rawA.subst υ₀ :: Ψ₀) υ₀.lift Γ Λ σ blocks pending Ψ υ inner chosen depth' ∧
      depth = depth'+1 ∧ ∀ e, plug e = ProofShape.mkApps (.lam rawA (inner e)) args) := by
  induction H with
  | base => omega
  | @retained Γ Λ σ blocks pending Ψ υ plug chosen depth A u y n cd rawA' remaining args H hA hy RD HA ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base => exact .inl ⟨A, u, y, rawA', args, remaining, n, cd, id, 0, 0,
          hA, hy, RD, HA, .base, rfl, rfl, fun _ => rfl⟩
    · rcases ih (by omega) with
        ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, inner, chosen', depth',
          hA₀, hy₀, RD₀, HA₀, HI, hc, hd', EW⟩ |
        ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, inner, depth', hp, hA₀, RD₀, HI, hd', EW⟩
      · exact .inl ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, _, chosen'+1, depth'+1,
          hA₀, hy₀, RD₀, HA₀, .retained HI hA hy RD HA, by omega, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
      · exact .inr ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, _, depth'+1,
          hp, hA₀, RD₀, .retained HI hA hy RD HA, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base => exact .inr ⟨A, u, rawA', args, n, cd, id, 0, rfl, hA, RD, .base,
          rfl, fun _ => rfl⟩
    · rcases ih (by omega) with
        ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, inner, chosen', depth',
          hA₀, hy₀, RD₀, HA₀, HI, hc, hd', EW⟩ |
        ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, inner, depth', hp, hA₀, RD₀, HI, hd', EW⟩
      · exact .inl ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, _, chosen', depth'+1,
          hA₀, hy₀, RD₀, HA₀, .unused HI hA RD, hc, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
      · exact .inr ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, _, depth'+1,
          hp, hA₀, RD₀, .unused HI hA RD, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩

/-- The source half of a paired chain gives an identity supply square. -/
theorem EqSupplyInsertionSquare.source_identity
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks) :
    EqSupplyInsertionSquare Γ Γ Δ σ σ VExpr.Subst.id ProofShape.Subst.id
      Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks blocks := by
  have W₀ := EqSpecializationFrame.of_conversion hΔ W.agree.left (.refl W.actual.wf)
  have J₀ := J.source_identity
  obtain ⟨hΛ, S, ES⟩ := J₀.actual W₀
  exact ⟨W₀, J₀, J₀, hΛ, S, ES, by intro e; simp only [VExpr.subst_id],
    by intro e; simp only [ProofShape.subst_id]⟩

/-- Align a chosen outer frame's source domain with its displayed annotation
before reading a later native suffix. The inner history is realized through
that identity conversion, so its wrapper is literally unchanged while all
pending supplies retain their source typings. The lower and upper current
contexts are returned with the same concrete identity square. -/
theorem EqPendingSupplyHistory.align_chosen_outer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hy : env.HasType univs Δ y (A.subst σ₀))
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ A)) rawA)
    (HA : EqRetainedArgumentSupply Γ₀ Δ σ₀ blocks₀ A y pending₀ remaining args)
    (H : EqPendingSupplyHistory D Δ (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y)
      blocks₀.underBinder remaining historyTarget historyMap Γ Λ σ blocks pending Ψ υ plug chosen depth) :
    ∃ B Γ' Λ' σ' outblocks normalized,
      env.IsDefEq univs Γ₀ A B (.sort u) ∧ env.HasType univs Δ y (B.subst σ₀) ∧
      blocks₀.erased (proofErase Γ₀ B) = rawA ∧
      EqRetainedArgumentSupply Γ₀ Δ σ₀ blocks₀ B y pending₀ remaining args ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
        Λ Λ' VExpr.Subst.id ProofShape.Subst.id blocks outblocks ∧
      EqPendingSupplyHistory D Δ (B :: Γ₀) (blocks₀.actual B :: Λ₀) (σ₀.cons y)
        blocks₀.underBinder remaining (proofEraseCtx (blocks₀.actual B :: Λ₀)) ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id normalized chosen depth ∧
      ∀ e, plug e = normalized e := by
  have Q₀ := EqSupplyInsertionSquare.source_identity hΔ W J
  obtain ⟨B, HAB, EB, Q, Eraw⟩ := Q₀.retained heq hs hΔ hA hy RD.forget
  have Q : EqSupplyInsertionSquare (A :: Γ₀) (B :: Γ₀) Δ (σ₀.cons y) (σ₀.cons y)
      VExpr.Subst.id ProofShape.Subst.id (blocks₀.actual A :: Λ₀) (blocks₀.actual B :: Λ₀)
      VExpr.Subst.id ProofShape.Subst.id blocks₀.underBinder blocks₀.underBinder := by
    simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using Q
  have hyB : env.HasType univs Δ y (B.subst σ₀) := by
    cases Q.lower.target with | cons _ _ h => exact h.hasType.1
  have HA' : EqRetainedArgumentSupply Γ₀ Δ σ₀ blocks₀ B y pending₀ remaining args := by
    simpa only [VExpr.subst_id, ProofShape.subst_id, List.map_id_fun', id] using HA.frame hΔ Q₀ HAB
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx (blocks₀.actual B :: Λ₀)) ProofShape.Subst.id
  obtain ⟨Γ', Λ', σ', outblocks, normalized, Qnew, _, HRout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  have Eχ := HR.forget.shape.2
  refine ⟨B, Γ', Λ', σ', outblocks, normalized, HAB, hyB, EB, HA', ?_, HRout, ?_⟩
  · simpa only [Eχ, actual_id_liftN, raw_id_liftN] using Qnew
  · intro e
    simpa only [Eχ, raw_id_liftN, ProofShape.subst_id] using EW e

/-- An unused outer domain can likewise be aligned with its displayed
annotation without introducing a chosen image. The lower base scope stays
fixed, while the upper base and all dependent inner annotations are realized.
The wrapper and both binder counts remain unchanged. -/
theorem EqPendingSupplyHistory.align_unused_outer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Λ₀ A (.sort u))
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀) (proofErase Λ₀ A) rawA)
    (H : EqPendingSupplyHistory D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
      historyTarget historyMap Γ Λ σ blocks pending Ψ υ plug chosen depth) :
    ∃ B Γ' Λ' σ' outblocks normalized,
      env.IsDefEq univs Λ₀ A B (.sort u) ∧ proofErase Λ₀ B = rawA ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
        Λ Λ' VExpr.Subst.id ProofShape.Subst.id blocks outblocks ∧
      EqPendingSupplyHistory D Δ Γ₀ (B :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
        (proofEraseCtx (B :: Λ₀)) ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id normalized chosen depth ∧
      ∀ e, plug e = normalized e := by
  have Q₀ := EqSupplyInsertionSquare.source_identity hΔ W J
  obtain ⟨B, HAB, EB, Q, Eraw⟩ := Q₀.unused heq hs hΔ hA RD.forget
  have Q : EqSupplyInsertionSquare Γ₀ Γ₀ Δ σ₀ σ₀ VExpr.Subst.id ProofShape.Subst.id
      (A :: Λ₀) (B :: Λ₀) VExpr.Subst.id ProofShape.Subst.id
      (blocks₀ ++ [(1,0)]) (blocks₀ ++ [(1,0)]) := by
    simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using Q
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx (B :: Λ₀)) ProofShape.Subst.id
  obtain ⟨Γ', Λ', σ', outblocks, normalized, Qnew, _, HRout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  have Eχ := HR.forget.shape.2
  refine ⟨B, Γ', Λ', σ', outblocks, normalized, HAB, EB, ?_, HRout, ?_⟩
  · simpa only [Eχ, actual_id_liftN, raw_id_liftN] using Qnew
  · intro e
    simpa only [Eχ, raw_id_liftN, ProofShape.subst_id] using EW e

/-- The identity square produced by annotation alignment preserves the exact
chosen Eq spine in its new concrete contexts. Its type, nonproof status and
inserted raw vector are retained, so the actual counted body path can be reused
at the same raw source without an extra component-computation premise. -/
theorem EqSupplyInsertionSquare.identity_prefix
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
      Λ Λ' VExpr.Subst.id ProofShape.Subst.id incoming outgoing)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :
    EqPrefixSpecializationAt Γ' Δ v w v' w' original pre σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
      ((pre.map (proofErase Γ')).map outgoing.erased) =
        ((pre.map (proofErase Γ)).map incoming.erased) := by
  obtain ⟨HP, ht, EE⟩ := H.frame hΔ Q.lower hf
  simp only [VExpr.subst_id, ProofShape.subst_id, List.map_id_fun', id] at HP ht EE
  have EF : proofErase Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) =
      proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) := by
    simpa only [VExpr.subst_id, ProofShape.subst_id] using
      proofErase_subst_with Q.lower.target.wf Q.lower.actual hf Q.lower.erase
  refine ⟨HP, ht, ?_, ?_⟩
  · intro hp
    exact hn (proofErase_eq_proof.1 (EF.symm.trans (proofErase_eq_proof.2 hp)))
  · rw [EE]
    apply List.map_congr_left
    intro e he
    simpa only [ProofShape.subst_id] using (Q.erased e).symm

end Lean4Lean.VEnv.Strengthening
