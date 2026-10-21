import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionEqDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier

/-! # Primitive-free Eq beta peaks expose individual front instances

Only the final argument of each Eq proposition contracts: both carrier and
anchor stay fixed. Literal unit identity applications have a primitive-free
source comparison. A target union comparison exposes the converted probe
carrier and therefore descends the specified proposition equation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private identity_erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier
variable [Params]

/-- A concrete Eq beta peak for one lifted proposition equation. The source
comparison has no primitive steps; carrier and repeated anchor do not change.
Only the two displayed unit-identity arguments contract. Any union certificate
at the target pair proves the original proposition equation below the inserted
context. This does not assert such a target certificate exists. -/
theorem unit_probe_primitive_free_eq_beta_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN n) (Q.liftN n)) :
    let K := eqTypeProbe (.succ u) (.const family ls) (P.liftN n) (Q.liftN n) q
    let x := VExpr.app (.lam (.const family ls) (.bvar 0)) (.bvar i)
    let y := VExpr.app (.lam (.const family ls) (.bvar 0)) (.bvar j)
    let L := eqApp (.succ u) K (.bvar i) x
    let R := eqApp (.succ u) K (.bvar i) y
    let L' := eqApp (.succ u) K (.bvar i) (.bvar i)
    let R' := eqApp (.succ u) K (.bvar i) (.bvar j)
    env.HasType univs Γ' L (.sort .zero) ∧ env.HasType univs Γ' R (.sort .zero) ∧
      env.HasType univs Γ' L' (.sort .zero) ∧ env.HasType univs Γ' R' (.sort .zero) ∧
      JointCompare (fun _ _ _ => False) (proofEraseCtx Γ') true (proofErase Γ' L) (proofErase Γ' R) ∧
      ProofShape.BetaRed (proofErase Γ' L) (proofErase Γ' L') ∧
      ProofShape.BetaRed (proofErase Γ' R) (proofErase Γ' R') ∧
      (JointCompare (ErasedJointUnion D) (proofEraseCtx Γ') true
        (proofErase Γ' L') (proofErase Γ' R') → env.IsDefEqU univs Γ P Q) := by
  dsimp only
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have hK := HE.hasType.1
  have hu := hK.sort_r henv hΓ'
  have hiK := HE.symm.defeq hiT
  have hjK := HE.symm.defeq hjT
  obtain ⟨hxS, Ex⟩ := identity_erasures hΓ' hSw hiT
  obtain ⟨hyS, Ey⟩ := identity_erasures hΓ' hSw hjT
  have hxK := HE.symm.defeq hxS
  have hyK := HE.symm.defeq hyS
  have hL := HasType.eqApp heq hu hK hiK hxK
  have hR := HasType.eqApp heq hu hK hiK hyK
  have hL' := HasType.eqApp heq hu hK hiK hiK
  have hR' := HasType.eqApp heq hu hK hiK hjK
  have HC : JointCompare (fun _ _ _ => False) (proofEraseCtx Γ') true
      (proofErase Γ' (.app (.lam (.const family ls) (.bvar 0)) (.bvar i)))
      (proofErase Γ' (.app (.lam (.const family ls) (.bvar 0)) (.bvar j))) := by
    rw [Ex, Ey]
    have HR : ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Γ')
        (.lam (.const family ls) (.bvar 0)) (.forallE (.const family ls) (.const family ls)) :=
      .lam .bvar
    exact .appCarrier HR (.leaf .refl) (.carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm))
  have RB (k) : VExpr.BetaRed (.app (.lam (.const family ls) (.bvar 0)) (.bvar k)) (.bvar k) := by
    simpa [VExpr.inst, instVar, VExpr.liftN_zero] using
      (VExpr.BetaRed.beta (A := .const family ls) (b := .bvar 0) (a := .bvar k))
  refine ⟨hL, hR, hL', hR', ?_, ?_, ?_, ?_⟩
  · rw [proofErase_eqProofType heq hu hΓ' hK hiK hxK,
      proofErase_eqProofType heq hu hΓ' hK hiK hyK]
    exact .app (.leaf .refl) HC
  · exact proofErase_beta_forward hΓ' hL (VExpr.BetaRed.app .refl (RB i))
  · exact proofErase_beta_forward hΓ' hR (VExpr.BetaRed.app .refl (RB j))
  · intro HT
    have HG := proofErase_joint_union_eq_carrier_decode heq hu hs
      (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
      hΓ' hK hiK hiK hiK hjK HT
    have Ei : proofErase Γ' (.bvar i) = .bvar i :=
      if_neg (not_proof_at_positive_type hΓ' hSw hiT)
    have Ej : proofErase Γ' (.bvar j) = .bvar j :=
      if_neg (not_proof_at_positive_type hΓ' hSw hjT)
    rw [Ei, Ej] at HG
    rcases JointCarrierGuard.checked_or_exposed HG with Hcmp | ⟨B, R, HB, _⟩
    · exact (hne (Hcmp.bvar_injective erased_joint_union_head)).elim
    exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
      hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Every candidate proposition-front instance produces a typed primitive-free
Eq beta peak in an explicitly extended context. Certifying its beta-reduced
pair in the full union suffices to solve that exact original instance. Only a
closed positive empty structure is added to the standard Eq/definition
assumptions; no declared identity constant or global beta law is used. -/
theorem proposition_front_instance_primitive_free_eq_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.IsType univs Γ A)
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (HPQ : env.IsDefEqU univs (A :: Γ) P.lift Q.lift) :
    ∃ Δ L R L' R', OnCtx Δ (env.IsType univs) ∧
      env.HasType univs Δ L (.sort .zero) ∧ env.HasType univs Δ R (.sort .zero) ∧
      env.HasType univs Δ L' (.sort .zero) ∧ env.HasType univs Δ R' (.sort .zero) ∧
      JointCompare (fun _ _ _ => False) (proofEraseCtx Δ) true (proofErase Δ L) (proofErase Δ R) ∧
      ProofShape.BetaRed (proofErase Δ L) (proofErase Δ L') ∧
      ProofShape.BetaRed (proofErase Δ R) (proofErase Δ R') ∧
      (JointCompare (ErasedJointUnion D) (proofEraseCtx Δ) true
        (proofErase Δ L') (proofErase Δ R') → env.IsDefEqU univs Γ P Q) := by
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
    have H := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using H
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using HT.weakN henv WX⟩
  exact ⟨_, _, _, _, _, hΓE,
    unit_probe_primitive_free_eq_beta_peak heq hs hregistry hEq hRec hi hp hx hf
      hΓ hΓE W4 (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4⟩

end Lean4Lean.VEnv.Strengthening
