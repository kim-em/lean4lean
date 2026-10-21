import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary

/-! # Future carrier application contains the proposition front

Common future certificates fail shared application at unit results. Keeping
the result carrier avoids that literal counterexample, but a type-converted
selector hides the unit behind an Eq probe. Future carrier application then
has to expose that probe, which already descends proposition equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private selector_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- Missing shared-argument application law with a future carrier result.
The input is a full future common function certificate. This law is not
established or claimed smaller than PropositionFront; its output must retain
beta paths so that applications can be consumed again. -/
def TypedFutureCarrierApplication
    (Source Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ f g x A B}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ f (.forallE A B) → env.HasType univs Γ g (.forallE A B) →
    env.HasType univs Γ x A →
    BetaStableFamily (fun Δ => JointCompare Source Δ true) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) →
    BetaStableCarrier Target (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x))

/-- Shared application with future carrier output descends a proposition
equation hidden in the actual result type. The input selector certificate
works even at source False; the shared argument is the unit identity. -/
theorem TypedFutureCarrierApplication.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Happ : TypedFutureCarrierApplication Source (ErasedJointUnion D))
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
    env.IsDefEqU univs Γ P Q := by
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  let T := eqTypeProbe (.succ u) S (P.liftN n) (Q.liftN n) q
  have hSw : env.HasType univs Γ' S (.sort (.succ u)) := hS.weakN henv W
  have HE : env.IsDefEq univs Γ' T S (.sort (.succ u)) :=
    eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have hF : env.HasType univs Γ' F (.sort (.imax (.succ u) (.succ u))) :=
    .forallE hSw (hSw.weak henv)
  have hid : env.HasType univs Γ' (.lam S (.bvar 0)) F := .lam hSw (.bvar .zero)
  have hfi : env.HasType univs Γ' (.lam F (.app (.bvar 0) (.bvar (i + 1))))
      (.forallE F T.lift) := by
    apply HasType.lam hF
    apply (HE.symm.weak henv).defeq
    apply HasType.app (show env.HasType univs (F :: Γ') (.bvar 0) F from .bvar .zero)
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hiT.weak (B := F) henv
  have hgj : env.HasType univs Γ' (.lam F (.app (.bvar 0) (.bvar (j + 1))))
      (.forallE F T.lift) := by
    apply HasType.lam hF
    apply (HE.symm.weak henv).defeq
    apply HasType.app (show env.HasType univs (F :: Γ') (.bvar 0) F from .bvar .zero)
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hjT.weak (B := F) henv
  obtain ⟨hfi₀, Efi⟩ := selector_typing hΓ' hSw hiT
  obtain ⟨hgj₀, Egj⟩ := selector_typing hΓ' hSw hjT
  have HC := Happ hΓ' hfi hgj hid (by
    rw [Efi, Egj]
    exact unit_selector_family hi hp hx hf)
  simp only [VExpr.inst_lift] at HC
  have RI := proofErase_beta_forward hΓ' (HasType.app hfi₀ hid) (BetaRed.trans .beta .beta)
  have RJ := proofErase_beta_forward hΓ' (HasType.app hgj₀ hid) (BetaRed.trans .beta .beta)
  have HG := HC.1 ProofShape.BetaRed.refl RI RJ
  simp only [VExpr.liftN_zero, VExpr.inst, VExpr.instVar_upper, VExpr.instVar_zero] at HG
  rw [show proofErase Γ' (.bvar i) = .bvar i from
    if_neg (not_proof_at_positive_type hΓ' hSw hiT),
    show proofErase Γ' (.bvar j) = .bvar j from
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)] at HG
  rcases HG.checked_or_exposed with Hcmp | ⟨B, R, HB, _⟩
  · exact (hne (Hcmp.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Shared application with future carrier output already implies the full
proposition front in the presence of a closed positive empty structure. Even
source False suffices for this implication. This is a conditional obstruction
to claiming a smaller obligation, not a proof of application or strictness. -/
theorem TypedFutureCarrierApplication.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Happ : TypedFutureCarrierApplication Source (ErasedJointUnion D))
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
  exact Happ.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4


end Lean4Lean.VEnv.Strengthening
