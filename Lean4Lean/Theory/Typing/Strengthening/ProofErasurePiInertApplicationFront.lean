import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAnchoredRecognition
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionReadoutBoundary

/-! # Finite Pi-inert application still contains the proposition front

The completed Eq recognizer reads actual type-probe exposure at any finite
Pi-inert stage. Applied to the existing converted-unit selector, this shows
that unrestricted finite shared application and fresh-body extraction each
imply PropositionFront when a closed positive empty structure is present.
These are conditional lower bounds, not proofs of coverage or strict smallness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private constant_motive_lift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
variable [Params] {D : Definitions}

/-- Any actual finite Pi-inert carrier exposure of a lifted type-valued Eq
probe descends its original proposition indices. The equality major lives only
in the upper context. No path-coverage or function-application premise is used. -/
theorem pi_inert_type_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ') (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count)))
    (R : ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe u (S.liftN count) (P.liftN count) (Q.liftN count) q)) out)
    (HE : CarrierExposure out) : env.IsDefEqU univs Γ P Q := by
  have hSw := hS.weakN henv W
  have hPw := hP.weakN henv W
  have hQw := hQ.weakN henv W
  have E := eqTypeProbe_erase heq hΓ' hSw hPw hQw hq
  have R' := R
  rw [E] at R'
  have HT : ControlTyping (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [.succ u, .succ .zero])
        [.sort .zero, proofErase Γ' (P.liftN count),
          proofErase Γ' (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN count) (.sort u)),
          proofErase Γ' (S.liftN count), proofErase Γ' (Q.liftN count), .proof]) (.sort u) :=
    ⟨Γ', _, hΓ', rfl, eqTypeProbe_typed heq hΓ' hSw hPw hQw hq, E⟩
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  have hM := constantEqMotive_typed henv.ordered heq (by trivial)
    (HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .zero) (by trivial)) hP
    (HasType.sort (l := u) (hS.sort_r henv hΓ))
  have EM : proofErase Γ'
      (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN count) (.sort u)) =
      (proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u))).liftN count := by
    rw [← proofErase_liftN hΓ hΓ' W hM]
    congr 1
    simpa only [VExpr.liftN] using (constant_motive_lift (n := count)
      (w := VLevel.succ .zero) (α := VExpr.sort .zero) (a := P) (T := VExpr.sort u)).symm
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  exact (pi_inert_lifted_eq_probe_descend heq hs hreg hoff hRec hΓ hΓ' W ht hn
    (by simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ,
      proofErase_liftN hΓ hΓ' W hS, EM, ES, ProofShape.liftN]) HT R' HE).toU

/-- Finite shared application exposes a type-converted unit probe and therefore
reads the lower proposition equation. The input selector history already has
stage zero; the output may use any finite stage. The source assigned Pi alone
contains no explicit comparison of the hidden proposition indices. -/
theorem FinitePiInertSharedApplication.unit_probe_descend
    (Happ : FinitePiInertSharedApplication D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN count) (Q.liftN count)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  obtain ⟨stage, out, R, HEout⟩ := Happ.unit_conversion_exposure
    heq hi hp hx hf hD hΓ' hSw HE hiT hjT hne
  exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HEout

/-- Universal shared application already implies the full proposition front
in environments with a closed positive empty structure, even when it may choose
any finite output stage. This implication uses the proved recognizer, with no
assumed exposure-readout principle. It proves neither closure nor strict smallness. -/
theorem FinitePiInertSharedApplication.propositionFront_of_closed_unit
    (Happ : FinitePiInertSharedApplication D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
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
  exact Happ.unit_probe_descend heq hs hreg hoff hRec hi hp hx hf hD hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

/-- Hereditary fresh-body extraction has the same full proposition-front
consequence because it implies shared application. This is a lower bound on
the remaining coverage law, not a proof or a strict-smallness claim. -/
theorem FinitePiInertFunctionBodyReadout.propositionFront_of_closed_unit
    (Hbody : FinitePiInertFunctionBodyReadout D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront :=
  FinitePiInertSharedApplication.propositionFront_of_closed_unit
    (FinitePiInertFunctionBodyReadout.shared_application Hbody) heq hs hreg hoff hRec hi hp hx hf hD hS

end Lean4Lean.VEnv.Strengthening
