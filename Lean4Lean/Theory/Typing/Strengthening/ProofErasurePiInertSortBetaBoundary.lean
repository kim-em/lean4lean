import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUnitSynthesis

/-! # Proposition-only beta closure still exposes converted carriers

The new frame readout does not extend automatically to arbitrary sort-typed
comparisons. A predicate assigned a converted domain tests the native carrier
after a single beta step. This file retains the complete current checker,
including computed-lambda application and sort-root primitives.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private constant_motive_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params] {D : Definitions}

/-- A Pi-inert path from a neutral unary application computes only its argument.
The relation may have sort-root primitives; no global primitive-head premise is
needed. -/
theorem ProofShape.ScopedCompute.pi_inert_bvar_app_inv
    (R : ScopedCompute (PiInertStage D n) Δ (.app (.bvar f) x) out) :
    ∃ x', out = .app (.bvar f) x' ∧ ScopedCompute (PiInertStage D n) Δ x x' := by
  generalize E : ProofShape.app (.bvar f) x = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing f x with
  | refl => exact ⟨_, E.symm, .refl⟩
  | base H =>
    rcases H.2 with H | ⟨u, H⟩
    · cases E; exact H.elim
    · cases E.trans H
  | trans R S ihR ihS =>
    obtain ⟨x', rfl, RX⟩ := ihR E
    obtain ⟨x'', EO, SX⟩ := ihS rfl
    exact ⟨_, EO, RX.trans SX⟩
  | app RF RX =>
    cases E
    obtain rfl := RF.pi_inert_bvar_fixed
    exact ⟨_, rfl, RX⟩
  | beta | proj | lam | forallE => cases E

/-- Every rule of the computed checker preserves the native domain obligation
at a neutral predicate application. The computed-lambda rule cannot apply to a
variable, even with arbitrary computation prefixes. -/
theorem ProofShape.ComputedJointCompare.pi_inert_bvar_app_carrier
    (HO : contextOracle Δ f = .forallE A B)
    (H : ComputedJointCompare (PiInertStage D n) Δ mode
      (.app (.bvar f) x) (.app (.bvar f) y)) :
    ComputedJointCarrierGuard (PiInertStage D n) Δ A x y := by
  generalize EL : ProofShape.app (.bvar f) x = a at H
  generalize ER : ProofShape.app (.bvar f) y = b at H
  change ComputedJointCheck _ Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing f x y mode A B with
  | leaf H =>
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (EL.trans ER.symm)).2
      rw [E]
      exact .carrierChecked (.leaf .refl)
    | sort | const => cases EL
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EL.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases ER.trans E
  | app HF HX => cases EL; cases ER; exact .carrierChecked HX
  | appCarrier R HF HX =>
    cases EL; cases ER
    have RT := R.bvar_compute
    rw [HO] at RT
    obtain ⟨A', B', E, RA⟩ := RT.forallE_domain_inv_of_no_root (fun H => pi_inert_stage_no_pi H)
    cases E
    exact .carrierCompute RA HX
  | appComputed R HF HX =>
    cases EL; cases ER
    have E := R.pi_inert_bvar_fixed
    cases E
  | compute RX RY HC ih =>
    obtain ⟨x', EX, RX'⟩ := (EL ▸ RX).pi_inert_bvar_app_inv
    obtain ⟨y', EY, RY'⟩ := (ER ▸ RY).pi_inert_bvar_app_inv
    exact .carrierReduce RX' RY' (ih HO EX.symm EY.symm hk)
  | symm HC ih => exact .carrierSymm (ih HO ER EL hk)
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases ER
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EL
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- Proposed beta closure only for actual propositions and stage-zero raw
comparisons. The output may choose any finite stage and need not be hereditary.
This is an unproved obligation, not a consequence of the frame theorem. -/
def FinitePiInertPropositionBeta (D : Definitions) : Prop :=
  ∀ {Γ P Q left right}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) →
    ProofShape.BetaRed (proofErase Γ P) left → ProofShape.BetaRed (proofErase Γ Q) right →
    ∃ n, ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true left right

/-- Even proposition-only beta closure moves a supplied guard from an assigned
domain to a neutral predicate's native domain. The source uses a displayed eta
wrapper and the computed-lambda application rule at stage zero. -/
theorem FinitePiInertPropositionBeta.native_domain_guard
    (Hbeta : FinitePiInertPropositionBeta D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (hl : Lookup Γ f (.forallE B (.sort .zero)))
    (hfA : env.HasType univs Γ (.bvar f) (.forallE A (.sort .zero)))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ∃ n, ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have hn := not_isProof_function_to_sort hΓ hfA
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg hn
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, v, hB⟩
  have hPiB := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have EPiB : proofErase Γ (.forallE B (.sort .zero)) = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPiB),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))]
  have HO : contextOracle (proofEraseCtx Γ) f = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl, EPiB]
  let body := VExpr.app (VExpr.bvar f).lift (.bvar 0)
  let wrapper := VExpr.lam A body
  have hb : env.HasType univs (A :: Γ) body (.sort .zero) := by
    simpa only [body, lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using
      HasType.app (hfA.weak henv (B := A)) (HasType.bvar Lookup.zero)
  have hw : env.HasType univs Γ wrapper (.forallE A (.sort .zero)) := .lam hA hb
  have EW : proofErase Γ wrapper = .lam (proofErase Γ A) (proofErase (A :: Γ) body) :=
    if_neg (not_isProof_function_to_sort hΓ hw)
  have hlx := hw.app hx
  have hly := hw.app hy
  have HL : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ (.app wrapper x)) (proofErase Γ (.app wrapper y)) := by
    rw [show proofErase Γ (.app wrapper x) = .app _ _ from if_neg (not_isProof_of_sort hΓ hlx),
      show proofErase Γ (.app wrapper y) = .app _ _ from if_neg (not_isProof_of_sort hΓ hly)]
    apply ComputedJointCheck.appComputed (A := proofErase Γ A) (body := proofErase (A :: Γ) body)
    · rw [EW]; exact .refl
    · exact .leaf .refl
    · exact HX
  have RP : ProofShape.BetaRed (proofErase Γ (.app wrapper x)) (proofErase Γ (.app (.bvar f) x)) := by
    simpa only [body, wrapper, VExpr.inst, instVar_zero, inst_lift] using
      proofErase_beta_forward hΓ hlx (VExpr.BetaRed.beta (A := A) (b := body) (a := x))
  have RQ : ProofShape.BetaRed (proofErase Γ (.app wrapper y)) (proofErase Γ (.app (.bvar f) y)) := by
    simpa only [body, wrapper, VExpr.inst, instVar_zero, inst_lift] using
      proofErase_beta_forward hΓ hly (VExpr.BetaRed.beta (A := A) (b := body) (a := y))
  obtain ⟨n, HC⟩ := Hbeta hΓ hlx hly HL RP RQ
  rw [show proofErase Γ (.app (.bvar f) x) = .app _ _ from if_neg (not_isProof_of_sort hΓ (hfA.app hx)),
    show proofErase Γ (.app (.bvar f) y) = .app _ _ from if_neg (not_isProof_of_sort hΓ (hfA.app hy)), EF] at HC
  exact ⟨n, HC.pi_inert_bvar_app_carrier HO⟩

/-- Proposition-only beta closure applied to an observer declared over a
lifted Eq probe descends the original proposition equation. Only a stage-zero
unit guard is supplied; the promised output may use any finite stage. -/
theorem FinitePiInertPropositionBeta.native_probe_descend
    (Hbeta : FinitePiInertPropositionBeta D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count)))
    (hl : Lookup Γ' f (.forallE
      (eqTypeProbe (.succ u) (.const family ls) (P.liftN count) (Q.liftN count) q) (.sort .zero)))
    (hf : env.HasType univs Γ' (.bvar f) (.forallE (.const family ls) (.sort .zero)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have hT := eqTypeProbe_typed heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq
  have HG : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ')
      (proofErase Γ' (.const family ls)) (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j)) := by
    rw [show proofErase Γ' (.const family ls) = .const family ls from if_neg (not_isProof_of_sort hΓ' hSw)]
    exact .carrierSubsingleton (.unit hi hx hfields (ps := []) hp.symm)
  obtain ⟨n, HK⟩ := Hbeta.native_domain_guard hΓ' hSw hT hl hf hiT hjT HG
  rw [show proofErase Γ' (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ' hSw hiT),
    show proofErase Γ' (.bvar j) = .bvar j from if_neg (not_proof_at_positive_type hΓ' hSw hjT)] at HK
  rcases HK.checked_or_exposed with HC | ⟨out, R, HE, _⟩
  · exact (hne HC.pi_inert_bvar_injective).elim
  · exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HE

/-- An observer binder can be constructed from the probe's actual semantic
conversion. No native recovery or raw comparison of that conversion is supplied.
Hence the missing beta law alone must recover the lower proposition equation. -/
theorem FinitePiInertPropositionBeta.unit_probe_descend
    (Hbeta : FinitePiInertPropositionBeta D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN count) (Q.liftN count)) :
    env.IsDefEqU univs Γ P Q := by
  let S := VExpr.const family ls
  let T := eqTypeProbe (.succ u) S (P.liftN count) (Q.liftN count) q
  let F := VExpr.forallE T (.sort .zero)
  have hSw : env.HasType univs Γ' S (.sort (.succ u)) := hS.weakN henv W
  have HE : env.IsDefEq univs Γ' T S (.sort (.succ u)) :=
    eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have hF : env.HasType univs Γ' F (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallE HE.hasType.1 (.sort (by trivial))
  have hΓF : OnCtx (F :: Γ') (env.IsType univs) := ⟨hΓ', _, hF⟩
  have HFS : env.IsDefEq univs Γ' F (.forallE S (.sort .zero))
      (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallEDF HE (.sortDF (by trivial) (by trivial) rfl)
  have hf : env.HasType univs (F :: Γ') (.bvar 0) (.forallE S (.sort .zero)) := by
    simpa only [S, VExpr.lift, VExpr.liftN] using
      (HFS.weak henv (B := F)).defeq (HasType.bvar (Lookup.zero (ty := F)))
  have ET : T.lift = eqTypeProbe (.succ u) S (P.liftN (count+1)) (Q.liftN (count+1)) q.lift := by
    simp only [T, eqTypeProbe, eqRecApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN,
      constant_motive_lift, S]
  have hlookup : Lookup (F :: Γ') 0 (.forallE
      (eqTypeProbe (.succ u) S (P.liftN (count+1)) (Q.liftN (count+1)) q.lift) (.sort .zero)) := by
    have H : Lookup (F :: Γ') 0 (.forallE T.lift (.sort .zero)) := by
      simpa only [F, VExpr.lift, VExpr.liftN] using (Lookup.zero (ty := F) (Γ := Γ'))
    simpa only [ET] using H
  have hq' : env.HasType univs (F :: Γ') q.lift
      (eqApp (.succ .zero) (.sort .zero) (P.liftN (count+1)) (Q.liftN (count+1))) := by
    simpa only [HasType, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using hq.weak (B := F) henv
  have hi' : env.HasType univs (F :: Γ') (.bvar (i+1)) S := by
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hiT.weak (B := F) henv
  have hj' : env.HasType univs (F :: Γ') (.bvar (j+1)) S := by
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hjT.weak (B := F) henv
  exact Hbeta.native_probe_descend heq hs hreg hoff hRec hi hp hx hfields hΓ hΓF W.cons0
    hS hP hQ hq' hlookup hf hi' hj' (by omega)

/-- Beta closure of stage-zero comparisons of actual propositions implies the
full proposition front in an environment with a closed positive empty structure.
The output may choose any finite stage, and no future-stability premise is part
of the proposed law. Thus this sort-only generalization is not a strictly smaller
replacement for the original goal. -/
theorem FinitePiInertPropositionBeta.propositionFront_of_closed_unit
    (Hbeta : FinitePiInertPropositionBeta D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family ls
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hSA : env.HasType univs (A :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hSA⟩
  have hΓSS : OnCtx (S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓS, _, hSA.weak henv⟩
  have W3 : Ctx.LiftN 3 0 Γ (S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
  have hP3 : env.HasType univs (S :: S :: A :: Γ) (P.liftN 3) (.sort .zero) := hP.weakN henv W3
  have hQ3 : env.HasType univs (S :: S :: A :: Γ) (Q.liftN 3) (.sort .zero) := hQ.weakN henv W3
  let E := eqApp (.succ .zero) (.sort .zero) (P.liftN 3) (Q.liftN 3)
  have hE : env.HasType univs (S :: S :: A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP3 hQ3
  have hΓE : OnCtx (E :: S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓSS, _, hE⟩
  have W4 : Ctx.LiftN 4 0 Γ (E :: S :: S :: A :: Γ) := W3.cons0
  have hq : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    have h := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using h
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    have H := HT.weakN henv WX
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using H⟩
  exact Hbeta.unit_probe_descend heq hs hreg hoff hRec hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

end Lean4Lean.VEnv.Strengthening
