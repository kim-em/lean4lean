import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqFamilyGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-! # Reading the guard of a general canonical Eq prefix

The general singleton code at five supplied arguments contains the same
endpoint comparison as the specialized Eq rule. This is inversion of an
existing guard, not construction of one from semantic endpoint equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {C : SingletonPrefixCode}
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-- A valid general singleton code for the five-argument canonical Eq prefix
retains its literal family comparison beneath the fresh proof major. Code
generation and telescope realization determine that context exactly. -/
theorem SingletonPrefixCode.Valid.eq_five_family_guard
    (V : C.Valid) (heq : env.HasCanonicalEq)
    (hn : C.data.name = ``Eq.rec) (hl : C.levels = [v,w])
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hcalc : C.telescope ([α,a,M,m,b].map (proofErase Γ)) = some (domains,result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) domains ([α,a,M,m,b].map (proofErase Γ))) :
    Cmp (proofEraseCtx (eqApp w α a b :: Γ))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift a.lift))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift b.lift)) := by
  have hz : C.data.sourceLevel [v,w] ≈ .zero := hl ▸ V.zero
  have hS : C.data.singletonLayout env [v,w] = some C.layout := hl ▸ V.layout_eq
  have hE : C.data.propElim [v,w] = some C.elim := hl ▸ V.elim_eq
  have hg := eqRec_prefix_generated (α := α) (a := a) (M := M) (m := m) (b := b)
    (U := univs) heq V.registered hn hz hS hE
  have hg' := hg
  rw [← hl] at hg'
  have ht' : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) [α,a,M,m,b]) := by
    rw [hn, hl]
    exact ⟨_, ht⟩
  have hd := (Prod.mk.inj (Option.some.inj ((V.telescope_eq hΓ hg' ht').symm.trans hcalc))).1
  have HF := (V.guardWith_iff heq hΓ hg' ht').1 (hd ▸ HG)
  rw [hl] at HF
  exact (eqRec_family_guard_iff heq V.registered hn hz hS hE).1 HF

/-- At carrier Prop the general singleton family guard exposes a comparison
of the proposition indices in its fresh proof-major context. No head-exposure,
substitution-completeness, or endpoint-beta hypothesis is used to decode it. -/
theorem SingletonPrefixCode.Valid.eq_prop_five_guard_readout
    (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hn : C.data.name = ``Eq.rec) (hl : C.levels = [v,.succ .zero])
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hcalc : C.telescope ([.sort .zero,P,M,m,Q].map (proofErase Γ)) = some (domains,result))
    (HG : C.guardWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ) domains
      ([.sort .zero,P,M,m,Q].map (proofErase Γ))) :
    JointCompare Step (proofEraseCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)) true
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) P.lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) Q.lift) := by
  obtain ⟨_, _, _, hP, _, _, hQ⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hEQ := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, hEQ⟩
  have HG' := V.eq_five_family_guard heq hn hl hΓ ht hcalc HG
  exact proofErase_joint_eq_sort_decode heq (by trivial) hstep hhead hinert hΓE
    (hP.weak henv) (hP.weak henv) (hP.weak henv) (hQ.weak henv) HG'

/-- A general singleton primitive on a typed five-argument Prop-carrier Eq
prefix contains an endpoint comparison. The particular code, residual
telescope, output, and generation witness may all be existentially hidden. -/
theorem proofErase_singleton_eq_prop_five_readout
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q)) out) :
    JointCompare Step (proofEraseCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)) true
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) P.lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) Q.lift) := by
  generalize Es : proofErase Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) = source at H
  cases H with
  | intro V ha hcalc HG =>
    have hnp : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) := by
      intro hp
      have E := congrArg constHead (Es.symm.trans (proofErase_eq_proof.2 hp))
      simp only [constHead_mkApps, constHead] at E
      cases E
    have HE := proofErase_const_spine hΓ (args := [.sort .zero,P,M,m,Q]) ht hnp
    obtain ⟨hn, hl, hargs⟩ := ProofShape.const_spine_inj (HE.symm.trans Es)
    rw [← hargs] at hcalc HG
    exact V.eq_prop_five_guard_readout heq hstep hhead hinert hn.symm hl.symm hΓ ht hcalc HG

/-- When the endpoint propositions originate below an inserted front block,
the five-argument primitive's family certificate descends below that block and
the fresh proof-major binder together. No inhabitant of either binder is used. -/
theorem proofErase_singleton_eq_prop_five_descend
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (ht : env.HasType univs Γ'
      (eqRecBeforeMajor v (.succ .zero) (.sort .zero) (P.liftN n) M m (Q.liftN n)) T)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ')
      (proofErase Γ' (eqRecBeforeMajor v (.succ .zero) (.sort .zero)
        (P.liftN n) M m (Q.liftN n))) out) :
    env.IsDefEqU univs Γ P Q := by
  have hPw := hP.weakN henv W
  have hQw := hQ.weakN henv W
  have hE := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hPw hQw
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n) :: Γ')
      (env.IsType univs) := ⟨hΓ', _, hE⟩
  have HC := proofErase_singleton_eq_prop_five_readout heq hstep hhead hinert hΓ' ht H
  simp only [lift, liftN_liftN] at HC
  rw [proofErase_liftN hΓ hΓE W.cons0 hP, proofErase_liftN hΓ hΓE W.cons0 hQ] at HC
  exact (proofErase_joint_compare_descend hstep hΓ hΓE W.cons0 rfl hP hQ HC).1
    ⟨_, HasType.sort (by trivial)⟩

end Lean4Lean.VEnv.Strengthening
