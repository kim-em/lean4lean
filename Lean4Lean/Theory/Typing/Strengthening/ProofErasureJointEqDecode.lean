import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierPropositions
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypeExposure

/-! # Decoding equality propositions over a literal universe

At a literal sort, carrier checking contributes no extra comparison rules.
Canonical Eq also has a fixed native recovery type at this carrier. These
facts allow reading its final argument out of an inferred joint comparison,
without proposition beta stability or carrier-domain re-synthesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

private theorem erase_eq_type (hu : u.WF univs) :
    proofErase [] (canonicalEqType.instL [u]) =
      .forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) := by
  let Γ₁ : List VExpr := [.sort u]
  let Γ₂ : List VExpr := [.bvar 0, .sort u]
  let Γ₃ : List VExpr := [.bvar 1, .bvar 0, .sort u]
  have h₁ : OnCtx Γ₁ (env.IsType univs) := ⟨by trivial, _, HasType.sort hu⟩
  have ht₁ : env.HasType univs Γ₁ (.bvar 0) (.sort u) := .bvar .zero
  have h₂ : OnCtx Γ₂ (env.IsType univs) := ⟨h₁, _, ht₁⟩
  have ht₂ : env.HasType univs Γ₂ (.bvar 1) (.sort u) := .bvar (.succ .zero)
  have h₃ : OnCtx Γ₃ (env.IsType univs) := ⟨h₂, _, ht₂⟩
  have ht₃ := HasType.sort (env := env) (U := univs) (Γ := Γ₃) (l := .zero) (by trivial)
  have hPi₂ := HasType.forallE ht₂ ht₃
  have hPi₁ := HasType.forallE ht₁ hPi₂
  have hPi₀ := HasType.forallE (HasType.sort hu) hPi₁
  change proofErase [] (.forallE (.sort u) (.forallE (.bvar 0)
    (.forallE (.bvar 1) (.sort .zero)))) = _
  rw [show proofErase [] (.forallE (.sort u) (.forallE (.bvar 0)
    (.forallE (.bvar 1) (.sort .zero)))) = .forallE _ _ from
      if_neg (not_isProof_of_sort (by trivial) hPi₀)]
  rw [show proofErase [] (.sort u) = .sort u from
      if_neg (not_isProof_of_sort (by trivial) (HasType.sort hu))]
  rw [show proofErase Γ₁ (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) =
    .forallE _ _ from if_neg (not_isProof_of_sort h₁ hPi₁)]
  rw [show proofErase Γ₁ (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort h₁ ht₁)]
  rw [show proofErase Γ₂ (.forallE (.bvar 1) (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort h₂ hPi₂)]
  rw [show proofErase Γ₂ (.bvar 1) = .bvar 1 from if_neg (not_isProof_of_sort h₂ ht₂)]
  exact congrArg (ProofShape.forallE (.sort u))
    (congrArg (ProofShape.forallE (.bvar 0))
      (congrArg (ProofShape.forallE (.bvar 1)) (if_neg (not_isProof_of_sort h₃ ht₃))))

private theorem eq_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.const ``Eq [u]) T) :
    T = .forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) := by
  generalize E : ProofShape.const ``Eq [u] = e at R
  induction R with
  | const hc hw hl =>
    cases E
    have EE := Option.some.inj (heq.1.symm.trans hc)
    cases EE
    exact erase_eq_type (hw u (by simp))
  | convert _ H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
        ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
          ⟨fun _ H => hhead H, trivial⟩⟩⟩⟩
  | bvar | sort | lam | app | forallE | proj => cases E

private theorem eq_sort_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.app (.const ``Eq [u]) (.sort v)) T) :
    T = .forallE (.sort v) (.forallE (.sort v) (.sort .zero)) := by
  generalize E : ProofShape.app (.const ``Eq [u]) (.sort v) = e at R
  induction R with
  | app R =>
    cases E
    cases eq_recovery heq hhead R
    rfl
  | convert _ H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
        ⟨fun _ H => hhead H, trivial⟩⟩⟩
  | bvar | sort | const | lam | forallE | proj => cases E

private theorem eq_sort_prefix_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.app (.app (.const ``Eq [u]) (.sort v)) z) T) :
    T = .forallE (.sort v) (.sort .zero) := by
  generalize E : ProofShape.app (.app (.const ``Eq [u]) (.sort v)) z = e at R
  induction R with
  | app R =>
    cases E
    cases eq_sort_recovery heq hhead R
    rfl
  | convert _ H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨fun _ H => hhead H, trivial⟩⟩
  | bvar | sort | const | lam | forallE | proj => cases E

private def eqSort (u v : VLevel) (z a : ProofShape) : ProofShape :=
  .app (.app (.app (.const ``Eq [u]) (.sort v)) z) a

private theorem eq_sort_compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (R : ScopedCompute Step Δ (eqSort u v z a) out) :
    ∃ z' a', out = eqSort u v z' a' ∧
      ScopedCompute Step Δ z z' ∧ ScopedCompute Step Δ a a' := by
  change ScopedCompute Step Δ (mkApps (.const ``Eq [u]) [.sort v, z, a]) out at R
  obtain ⟨args, E, H⟩ := R.const_spine hn
  cases H with
  | cons Hv H => cases H with
    | cons Hz H => cases H with
      | cons Ha H =>
        cases H
        rw [Hv.sort_fixed hhead] at E
        exact ⟨_, _, E, Hz, Ha⟩

private theorem eq_sort_decode_raw
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (H : JointCheck Step Δ kind sa sb) (hm : kind = .compare false)
    (Ea : sa = eqSort u v z a) (Eb : sb = eqSort u' v' z' b) :
    JointCompare Step Δ true a b := by
  induction H generalizing u v z a u' v' z' b with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have EE := Ea.symm.trans Eb
      exact (ProofShape.app.inj EE).2 ▸ JointCheck.leaf ScopedLeaf.refl
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact HX
  | appCarrier R HF HX =>
    cases Ea
    cases Eb
    cases eq_sort_prefix_recovery heq hhead R
    exact JointCarrierGuard.sort_checked hhead HX
  | compute Ra Rb HC ih =>
    obtain ⟨za, aa, EA, Rza, Raa⟩ := eq_sort_compute hhead hn (Ea ▸ Ra)
    obtain ⟨zb, bb, EB, Rzb, Rbb⟩ := eq_sort_compute hhead hn (Eb ▸ Rb)
    exact .compute Raa Rbb (ih hm EA EB)
  | symm H ih => exact .symm (ih hm Eb Ea)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Inferred comparison of canonical equality propositions over literal sorts
compares their final arguments. Primitive computation must preserve Eq spines.
No typing, beta stability, confluence, or exact recovery of the arguments is
assumed, and the two Eq prefixes may use different endpoints and universes. -/
theorem ProofShape.JointCompare.eq_sort_decode
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (H : JointCompare Step Δ false
      (.app (.app (.app (.const ``Eq [u]) (.sort v)) z) a)
      (.app (.app (.app (.const ``Eq [u']) (.sort v')) z') b)) :
    JointCompare Step Δ true a b := eq_sort_decode_raw heq hhead hn H rfl rfl rfl

private theorem erase_eq_sort
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hz : env.HasType univs Γ z (.sort v)) (ha : env.HasType univs Γ a (.sort v)) :
    proofErase Γ (eqApp (.succ v) (.sort v) z a) =
      eqSort (.succ v) v (proofErase Γ z) (proofErase Γ a) := by
  have h0 : env.HasType univs Γ (.const ``Eq [.succ v])
      (.forallE (.sort (.succ v)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    simpa [canonicalEqType, VExpr.instL, VLevel.inst] using
      (HasType.const (Γ := Γ) heq.1 (ls := [.succ v]) (by intro l hl; cases List.mem_singleton.1 hl; exact hv) rfl)
  have h1 : env.HasType univs Γ (.app (.const ``Eq [.succ v]) (.sort v))
      (.forallE (.sort v) (.forallE (.sort v) (.sort .zero))) := by
    simpa [VExpr.inst, instVar, VExpr.liftN] using h0.app (HasType.sort hv)
  have h2 := h1.app hz
  have h3 : env.HasType univs Γ (eqApp (.succ v) (.sort v) z a) (.sort .zero) := h2.app ha
  have hn3 := not_isProof_of_sort hΓ h3
  have hn2 := not_isProof_fn hΓ h2 ha hn3
  have hn1 := not_isProof_fn hΓ h1 hz hn2
  have hn0 := not_isProof_fn hΓ h0 (HasType.sort hv) hn1
  unfold eqApp at hn3
  simp only [eqApp, proofErase, if_neg hn3, if_neg hn2, if_neg hn1, if_neg hn0,
    if_neg (not_isProof_of_sort hΓ (HasType.sort hv)), eqSort]

/-- Either comparison mode between typed Eq propositions over a literal sort
can be decoded at the final argument. Typed primitive replay rules out the
extra common-mode cases before the raw decoder is applied. -/
theorem proofErase_joint_eq_sort_decode
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hz : env.HasType univs Γ z (.sort v)) (hz' : env.HasType univs Γ z' (.sort v))
    (ha : env.HasType univs Γ a (.sort v)) (hb : env.HasType univs Γ b (.sort v))
    (H : JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp (.succ v) (.sort v) z a))
      (proofErase Γ (eqApp (.succ v) (.sort v) z' b))) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
  have HA := HasType.eqApp heq (show (VLevel.succ v).WF univs from hv) (HasType.sort hv) hz ha
  have HB := HasType.eqApp heq (show (VLevel.succ v).WF univs from hv) (HasType.sort hv) hz' hb
  have HC := proofErase_joint_types_inferred hstep hΓ HA HB H
  rw [erase_eq_sort heq hv hΓ hz ha, erase_eq_sort heq hv hΓ hz' hb] at HC
  exact JointCompare.eq_sort_decode heq hhead hn HC

/-- Missing restricted stability law: only the right endpoint Q of the
canonical diagonal comparison Eq Prop P P versus Eq Prop P Q is beta reduced.
The theorem below shows that this restriction is equivalent to full
proposition beta stability, so it does not give a smaller remaining front. -/
def JointEqPropBetaStability (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P Q Q'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ Q' (.sort .zero) →
    JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P P))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q)) →
    ProofShape.BetaRed (proofErase Γ Q) (proofErase Γ Q') →
    JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P P))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q'))

open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- Restricting beta stability to diagonal equality propositions over Prop
loses none of the original obligation. This uses no beta stability in its
encoding or decoding, only sound primitive replay and Eq-head exclusion. -/
theorem joint_eq_prop_beta_stability_iff
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out) :
    JointEqPropBetaStability Step ↔ JointPropBetaStability Step := by
  constructor
  · intro HE Γ P Q out hΓ hP hQ HC R
    obtain ⟨Q', RQ, EQ⟩ := proofErase_beta_replay hΓ hQ R
    have hQ' := (beta_eq hΓ hQ RQ).hasType.2
    have HR : ProofShape.BetaRed (proofErase Γ Q) (proofErase Γ Q') := EQ ▸ R
    have HG : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
        (proofErase Γ P) (proofErase Γ Q) := .carrierChecked HC
    have HP := proofErase_joint_carrier_propositions (mode := true) heq (show (VLevel.succ .zero).WF univs by trivial)
      hΓ (HasType.sort (by trivial)) hP hP hQ HG
    have HH := HE hΓ hP hQ hQ' HP HR
    rw [← EQ]
    exact proofErase_joint_eq_sort_decode heq (by trivial) hstep hhead hn hΓ hP hP hP hQ' HH
  · intro HB Γ P Q Q' hΓ hP hQ hQ' HC R
    have HP := HasType.eqApp heq (show (VLevel.succ .zero).WF univs by trivial)
      (HasType.sort (by trivial)) hP hP
    have HQ := HasType.eqApp heq (show (VLevel.succ .zero).WF univs by trivial)
      (HasType.sort (by trivial)) hP hQ
    apply HB hΓ HP HQ HC
    rw [erase_eq_sort heq (by trivial) hΓ hP hQ,
      erase_eq_sort heq (by trivial) hΓ hP hQ']
    exact .app .refl R

end Lean4Lean.VEnv.Strengthening
