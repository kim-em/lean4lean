import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaForward

/-! # Native generic functions expose eta below a binder

Abstracting a body over its surrounding binder makes the generic replacement a
function. Its declared Pi supplies exact native application, so eta can run on
the resulting body without a native certificate for the original body.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Exact recovery of the function assignment gives exact recovery of its
application. The supplied argument needs ordinary typing only. -/
theorem static_structure_exact_native_app
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B))) :
    ¬ IsProof Γ (.app f x) → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.app f x)) (proofErase Γ (B.inst x)) := by
  intro hn
  have RN := RF (not_isProof_fn hΓ hf hx hn)
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RN
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    proofErase_instN hΓA hx Ctx.InstN.zero hB]
  exact .app RN

/-- A native certificate at the displayed Pi computes ordinary eta exactly.
Proof functions need no certificate and are handled directly by erasure. -/
theorem static_structure_exact_native_eta
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) := by
  classical
  by_cases hp : IsProof Γ f
  · have hp' := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _⟩ := hPi.forallE_inv henv
  have RN := RF hp
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RN
  rw [proofErase_nativeEtaExpansion hΓ hA hf hp]
  exact .base (erased_static_structure_eta_expansion_union_eta
    (.intro RN (DomainSort.of_typed hΓ hA)))

/-- A computed body equation lifts beneath its unchanged typed lambda binder.
Proof lambdas are erased on both sides, so no retained-body assumption is needed. -/
theorem proofErase_scoped_compute_lam_eq
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEq univs (A :: Γ) b b' T)
    (R : ScopedCompute Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) (proofErase (A :: Γ) b')) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.lam A b)) (proofErase Γ (.lam A b')) := by
  have HL := IsDefEq.lamDF hA HE
  classical
  by_cases hp : IsProof Γ (.lam A b)
  · have hp' := (isProof_congr hΓ HL).1 hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  have hp' : ¬ IsProof Γ (.lam A b') := fun h => hp ((isProof_congr hΓ HL).2 h)
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hp,
    show proofErase Γ (.lam A b') = .lam _ _ from if_neg hp']
  exact .lam .refl R

/-- A generic function with two dependent Pi inputs computes to its nested
eta expansion. The inner function application has exact native recovery from
the outer generic declaration, in both proof-erasure modes. -/
theorem static_structure_generic_nested_eta
    (hΓ : OnCtx Γ (env.IsType univs))
    (hG : env.HasType univs Γ (.forallE A (.forallE B C)) (.sort w)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.forallE A (.forallE B C) :: Γ))
      (proofErase (.forallE A (.forallE B C) :: Γ) (.bvar 0))
      (proofErase (.forallE A (.forallE B C) :: Γ)
        (.lam A.lift (.lam (B.liftN 1 1) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))) := by
  let G := VExpr.forallE A (.forallE B C)
  have hΓG : OnCtx (G :: Γ) (env.IsType univs) := ⟨hΓ, w, hG⟩
  obtain ⟨⟨u, hA⟩, _, _⟩ := hG.forallE_inv henv
  have hA' := hA.weakN henv (Ctx.LiftN.one : Ctx.LiftN 1 0 Γ (G :: Γ))
  have hΓGA : OnCtx (A.lift :: G :: Γ) (env.IsType univs) := ⟨hΓG, u, hA'⟩
  have hg : env.HasType univs (G :: Γ) (.bvar 0) G.lift := .bvar .zero
  have hg' : env.HasType univs (A.lift :: G :: Γ) (.bvar 1) G.lift.lift := .bvar (.succ .zero)
  have hx : env.HasType univs (A.lift :: G :: Γ) (.bvar 0) A.lift.lift := .bvar .zero
  have hf : env.HasType univs (A.lift :: G :: Γ) (.app (.bvar 1) (.bvar 0))
      (.forallE (B.liftN 1 1) (C.liftN 1 2)) := by
    simpa only [G, VExpr.lift, VExpr.liftN, VExpr.inst, VExpr.inst_liftN_bvar] using HasType.app hg' hx
  have RF := static_structure_exact_native_app (D := D) hΓGA hg' hx
    (fun hn => proofErase_scoped_lookup_recovery hΓGA (.succ .zero) hn .refl)
  have RF' : ¬ IsProof (A.lift :: G :: Γ) (.app (.bvar 1) (.bvar 0)) →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A.lift :: G :: Γ))
        (proofErase (A.lift :: G :: Γ) (.app (.bvar 1) (.bvar 0)))
        (proofErase (A.lift :: G :: Γ) (.forallE (B.liftN 1 1) (C.liftN 1 2))) := by
    simpa only [G, VExpr.lift, VExpr.liftN, VExpr.inst, VExpr.inst_liftN_bvar] using RF
  have R₁ := static_structure_exact_native_eta (D := D) hΓG hg
    (fun hn => proofErase_scoped_lookup_recovery hΓG .zero hn .refl)
  have R₂ := proofErase_scoped_compute_lam_eq hΓG hA' (IsDefEq.eta hf).symm
    (static_structure_exact_native_eta hΓGA hf RF')
  exact R₁.trans R₂

/-- The nested generic eta expansion has the generic function's actual type. -/
theorem generic_nested_eta_typing
    (hΓ : OnCtx Γ (env.IsType univs))
    (hG : env.HasType univs Γ (.forallE A (.forallE B C)) (.sort w)) :
    env.HasType univs (.forallE A (.forallE B C) :: Γ)
      (.lam A.lift (.lam (B.liftN 1 1) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))
      (VExpr.forallE A (.forallE B C)).lift := by
  let G := VExpr.forallE A (.forallE B C)
  have hΓG : OnCtx (G :: Γ) (env.IsType univs) := ⟨hΓ, w, hG⟩
  obtain ⟨⟨u, hA⟩, _, _⟩ := hG.forallE_inv henv
  have hA' := hA.weakN henv (Ctx.LiftN.one : Ctx.LiftN 1 0 Γ (G :: Γ))
  have hg' : env.HasType univs (A.lift :: G :: Γ) (.bvar 1) G.lift.lift := .bvar (.succ .zero)
  have hx : env.HasType univs (A.lift :: G :: Γ) (.bvar 0) A.lift.lift := .bvar .zero
  have hf : env.HasType univs (A.lift :: G :: Γ) (.app (.bvar 1) (.bvar 0))
      (.forallE (B.liftN 1 1) (C.liftN 1 2)) := by
    simpa only [G, VExpr.lift, VExpr.liftN, VExpr.inst, VExpr.inst_liftN_bvar] using HasType.app hg' hx
  exact HasType.lam hA' (IsDefEq.eta hf).hasType.1

omit [Params] in
/-- Supplying an arbitrary lambda to the nested generic expansion beta-cleans
to eta of its body below the original binder. No normalization of that body is
required; only the administrative application introduced by abstraction reduces. -/
theorem generic_nested_eta_inst_beta (A B f : VExpr) :
    VExpr.BetaRed
      ((VExpr.lam A.lift (.lam (B.liftN 1 1) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))).inst (.lam A f))
      (.lam A (.lam B (.app f.lift (.bvar 0)))) := by
  simp only [VExpr.inst, VExpr.inst_liftN, VExpr.instVar,
    Nat.reduceLT, ↓reduceIte, VExpr.liftN, Nat.reduceAdd]
  apply VExpr.BetaRed.lam .refl
  apply VExpr.BetaRed.lam .refl
  apply VExpr.BetaRed.app _ .refl
  have E : (f.liftN 2 1).inst (.bvar 1) = f.lift := by
    have H := congrArg VExpr.lift (VExpr.inst_liftN_bvar f 0)
    simpa only [VExpr.lift_inst_hi, VExpr.lift, VExpr.liftN, liftVar,
      Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, VExpr.liftN'_liftN_hi] using H
  simpa only [E] using (VExpr.BetaRed.beta (A := A.liftN 2) (b := f.liftN 2 1) (a := .bvar 1))

end Lean4Lean.VEnv.Strengthening
