import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertificateStrengthening
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation

/-! # Paired head beta when the erased bodies omit the argument

Certificate descent removes the argument binder from each body computation.
Intermediate lambda annotations may change, and the arguments may be unrelated,
unrecoverable or nonjoining. The restriction is on the two original body
shapes: both must be lifts of lower typed terms. Bodies retaining the argument
remain outside this result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

omit [Params] in
private theorem inst_lift_body (a x : ProofShape) : (a.liftN 1).inst x = a := by
  simp only [inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]

omit [Params] in
private theorem eta_unused_body {A B a b : ProofShape}
    (H : EtaHead (.lam A (a.liftN 1)) (.lam B (b.liftN 1))) : ProofShape.BetaRed a b := by
  obtain ⟨A', arg, E, Harg⟩ := H.shape
  have Eb := (ProofShape.lam.inj E).2
  have Ei := congrArg (fun e => e.inst .proof) Eb
  rcases Harg with rfl | rfl <;>
    simp only [inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons, ProofShape.Subst.id_lift] at Ei <;>
    rw [Ei] <;>
    simpa only [inst_lift_body] using
      (ProofShape.BetaRed.beta (A := B) (b := b.liftN 1) (a := .proof))

/-- A typed lambda whose body erasure is a lift keeps that property throughout
computation. Its lower body computation is reconstructed at the same relation,
without moving a body certificate between converted binder annotations. -/
theorem proofErase_scoped_unused_lam_compute
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F) (ha : env.HasType univs Γ a T)
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = source)
    (E : source = .lam A ((proofErase Γ a).liftN 1)) :
    ∃ A' a', out = .lam A' ((proofErase Γ a').liftN 1) ∧
      env.IsDefEq univs Γ a a' T ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ a') := by
  induction R generalizing Γ f F a T A with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    rw [E] at H
    obtain ⟨A', body', Eout, _, RB⟩ := H.lam_inv
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv (Ef.trans E)
    obtain ⟨⟨u, hD⟩, _, _⟩ := hf.lam_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    obtain ⟨a', HE, RC, Ea'⟩ := proofErase_scoped_compute_certificate_descend hstep
      hΓ hΓD Ctx.LiftN.one ha rfl (ScopedCompute.beta RB)
    exact ⟨A', a', Eout.trans (congrArg (ProofShape.lam A') Ea'.symm), HE, RC⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, a₁, E₁, HA, RA⟩ := ih₁ hΓ hf ha EΓ Ef E
    obtain ⟨f₁, HF, Ef₁⟩ := proofErase_scoped_compute_realize hstep.descent hΓ hf EΓ Ef R₁
    obtain ⟨A₂, a₂, E₂, HA₂, RA₂⟩ := ih₂ hΓ HF.hasType.2 HA.hasType.2 EΓ Ef₁ E₁
    exact ⟨A₂, a₂, E₂, HA.trans HA₂, RA.trans RA₂⟩
  | lam RA RB =>
    cases E
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _, _⟩ := hf.lam_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    obtain ⟨a', HE, RC, Ea'⟩ := proofErase_scoped_compute_certificate_descend hstep
      hΓ hΓD Ctx.LiftN.one ha (by simp only [proofEraseCtx, ED, EΓ]) RB
    exact ⟨_, a', congrArg (ProofShape.lam _) Ea'.symm, HE, RC⟩
  | app | proj | forallE => cases E

private theorem unused_body_compare
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind sa sb) (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F) (hg : env.HasType univs Γ g G)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A ((proofErase Γ a).liftN 1))
    (ER : sb = .lam B ((proofErase Γ b).liftN 1)) :
    JointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b) := by
  induction H generalizing Γ f F g G a T b U A B with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      have E := ProofShape.liftN_inj.1 (ProofShape.lam.inj (EL.symm.trans ER)).2
      rw [E]
      exact .leaf .refl
    | sort | const => cases EL
  | lam HD HB ihD ihB | lamSorted SD SD' HD HB ihD ihB =>
    cases hk
    cases EL
    cases ER
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _, _⟩ := hf.lam_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact (proofErase_joint_compare_certificate_descend hstep hΓ hΓD Ctx.LiftN.one
      (by simp only [proofEraseCtx, ED, EΓ]) ha hb HB).2 rfl hna hnb
  | etaLams HD Heta ihD =>
    cases hk
    rw [EL, ER] at Heta
    rcases Heta with Heta | Heta
    · exact .compute (.beta (eta_unused_body Heta)) .refl (.leaf .refl)
    · exact .compute .refl (.beta (eta_unused_body Heta)) (.leaf .refl)
  | compute RF RG HC ih =>
    obtain ⟨A', a', Ea', HA, RA⟩ := proofErase_scoped_unused_lam_compute hstep hhead RF hΓ hf ha EΓ Ef EL
    obtain ⟨B', b', Eb', HB, RB⟩ := proofErase_scoped_unused_lam_compute hstep hhead RG hΓ hg hb EΓ Eg ER
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep.descent hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep.descent hΓ hg EΓ Eg RG
    exact .compute RA RB (ih hk hΓ HF.hasType.2 HG.hasType.2 HA.hasType.2 HB.hasType.2
      (mt (isProof_congr hΓ HA).2 hna) (mt (isProof_congr hΓ HB).2 hnb) EΓ Ef' Eg' Ea' Eb')
  | symm HC ih => exact (ih hk hΓ hg hf hb ha hnb hna EΓ Eg Ef ER EL).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | app | appCarrier | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute |
      carrierReduce | carrierNested => cases hk

/-- An inferred lambda comparison descends directly to its lower non-proof
bodies when their erasures omit the lambda binder. The two lower bodies and
functions may have independently supplied types. No argument is supplied and
no exact argument-type recovery or primitive substitution law is required. -/
theorem proofErase_joint_unused_lam_compare
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F) (hg : env.HasType univs Γ g G)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (Ef : proofErase Γ f = .lam A ((proofErase Γ a).liftN 1))
    (Eg : proofErase Γ g = .lam B ((proofErase Γ b).liftN 1))
    (H : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    JointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b) :=
  unused_body_compare hstep hhead H rfl hΓ hf hg ha hb hna hnb rfl rfl rfl Ef Eg

/-- Paired proposition-valued head beta needs no relation between the arguments
when both erased bodies omit the bound variable. Actual substitution supplies
the lower proposition representatives; certificate descent handles every
intermediate computation without recovering either argument's assigned type. -/
theorem proofErase_joint_unused_proposition_head_beta {rawB rawC : ProofShape}
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (Eb : proofErase (A :: Γ) b = rawB.liftN 1)
    (Ec : proofErase (E :: Γ) c = rawC.liftN 1)
    (H : JointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C, hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓE : OnCtx (E :: Γ) (env.IsType univs) := ⟨hΓ, v, hE⟩
  have hbp : env.HasType univs Γ (b.inst p) (.sort .zero) := by
    have HH := (show env.IsDefEqU univs Γ (.app (.lam A b) p) (b.inst p) from
      ⟨_, IsDefEq.beta hb hpA⟩).of_l henv hΓ (HasType.app hf hp)
    exact HH.hasType.2
  have hcq : env.HasType univs Γ (c.inst q) (.sort .zero) := by
    have HH := (show env.IsDefEqU univs Γ (.app (.lam E c) q) (c.inst q) from
      ⟨_, IsDefEq.beta hc hqE⟩).of_l henv hΓ (HasType.app hg hq)
    exact HH.hasType.2
  have Ebp : proofErase Γ (b.inst p) = rawB := by
    rw [proofErase_instN hΓA hpA Ctx.InstN.zero hb, Eb, inst_lift_body]
  have Ecq : proofErase Γ (c.inst q) = rawC := by
    rw [proofErase_instN hΓE hqE Ctx.InstN.zero hc, Ec, inst_lift_body]
  have hnf : ¬ IsProof Γ (.lam A b) := not_isProof_fn hΓ hf hp
    (not_isProof_of_sort hΓ (HasType.app hf hp))
  have hng : ¬ IsProof Γ (.lam E c) := not_isProof_fn hΓ hg hq
    (not_isProof_of_sort hΓ (HasType.app hg hq))
  exact (proofErase_joint_unused_lam_compare (A := proofErase Γ A) (B := proofErase Γ E) hstep hhead hΓ hf hg hbp hcq
    (not_isProof_of_sort hΓ hbp) (not_isProof_of_sort hΓ hcq)
    (by simp only [proofErase, if_neg hnf, Eb, Ebp])
    (by simp only [proofErase, if_neg hng, Ec, Ecq]) H).common

/-- The original finite stage closes paired proposition head beta for
argument-free erased bodies, with arbitrary typed argument images. No global
beta transport, argument recovery or primitive substitution is assumed. -/
theorem proofErase_joint_stage_unused_proposition_head_beta {rawB rawC : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (Eb : proofErase (A :: Γ) b = rawB.liftN 1)
    (Ec : proofErase (E :: Γ) c = rawC.liftN 1)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_unused_proposition_head_beta (erased_joint_stage_certificate_descent heq hs stage)
    (erased_joint_stage_head stage) hΓ hp hq hf hg Eb Ec H

/-- The full union closes paired proposition head beta for
argument-free erased bodies, with arbitrary typed argument images. No global
beta transport, argument recovery or primitive substitution is assumed. -/
theorem proofErase_joint_union_unused_proposition_head_beta {rawB rawC : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (Eb : proofErase (A :: Γ) b = rawB.liftN 1)
    (Ec : proofErase (E :: Γ) c = rawC.liftN 1)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_unused_proposition_head_beta (erased_joint_union_certificate_descent heq hs)
    (erased_joint_union_head) hΓ hp hq hf hg Eb Ec H

end Lean4Lean.VEnv.Strengthening
