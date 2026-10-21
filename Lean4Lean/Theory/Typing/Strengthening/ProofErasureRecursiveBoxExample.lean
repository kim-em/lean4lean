import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNeutralExample

/-! # Box alignment with function-valued fields and no joins

The parameter types have eta-different neutral input domains. Their Box types
cannot be related by the recursive Pi/neutral relation itself, but all typed
Box guards transport using the actual projection recipe and nested checking.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf types_equal normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private arrow_erase
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNeutralExample
open private BoxCarrierAlignment.erase_box
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxGuard
open private BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
open private NeutralTypeChange.const_spine
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralTypeChange
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- For an explicitly registered Box, non-neutral function parameters give
typed equal, inhabited record carriers with no union join. The record types are outside
NeutralTypeChange, yet all certified typed guards are equivalent. Thus
recursive transport of field guards covers a new carrier case, rather than
requiring the record types to satisfy the preceding Pi-only criterion. -/
theorem recursive_box_function_field_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B, OnCtx Γ' (env.IsType univs) ∧
      env.IsDefEq univs Γ' A B (.sort (.succ .zero)) ∧
      NeutralTypeChange 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      (∃ DA DB, A = .forallE DA (.sort .zero) ∧ B = .forallE DB (.sort .zero)) ∧
      let TA := VExpr.app (.const family []) A
      let TB := VExpr.app (.const family []) B
      env.IsDefEq univs Γ' TA TB (.sort (.succ .zero)) ∧
      ¬ NeutralTypeChange 0 (proofErase Γ' TA) (proofErase Γ' TB) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' TA) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' TB) shared) ∧
      (∃ x, env.HasType univs Γ' x TA) ∧
      ∀ x y, env.HasType univs Γ' x TA → env.HasType univs Γ' y TA →
        (JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' TA) (proofErase Γ' x) (proofErase Γ' y) ↔
        JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' TB) (proofErase Γ' x) (proofErase Γ' y)) := by
  have hC := context_wf hΓ
  have Hparam : env.IsDefEq univs (context Γ)
      (.forallE assigned (.sort .zero)) (.forallE native (.sort .zero))
      (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) (.succ .zero) ≈ .succ .zero from rfl)).defeqDF
        (.forallEDF types_equal (HasType.sort (by trivial)))
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EFA := (arrow_erase hC types_equal.hasType.1).trans
    (congrArg (fun x => ProofShape.forallE x (.sort .zero)) EA)
  have EFN := (arrow_erase hC types_equal.hasType.2).trans
    (congrArg (fun x => ProofShape.forallE x (.sort .zero)) EN)
  have HT : NeutralTypeChange 0 (proofErase (context Γ) (.forallE assigned (.sort .zero)))
      (proofErase (context Γ) (.forallE native (.sort .zero))) := by
    rw [EFA, EFN]
    exact .forallE (.neutral (i := 1) (j := 1) (args := [_]) (args' := [_]) (by omega) (by omega)) .refl
  have Hbox := IsDefEq.appDF (BoxCarrierAlignment.family_typed (Γ := context Γ) hc) Hparam
  have EBA := (BoxCarrierAlignment.erase_box hc hC Hparam.hasType.1).trans
    (congrArg (ProofShape.app (.const family [])) EFA)
  have EBN := (BoxCarrierAlignment.erase_box hc hC Hparam.hasType.2).trans
    (congrArg (ProofShape.app (.const family [])) EFN)
  have hinert {Δ args out} : ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const family []) args) out :=
    fun H => erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)
  refine ⟨context Γ, _, _, hC, Hparam, HT, ⟨_, _, rfl, rfl⟩, Hbox, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [EBA, EBN] at H
    have HE := NeutralTypeChange.const_spine
      (show NeutralTypeChange 0 (ProofShape.mkApps (.const family []) [.forallE assignedRaw (.sort .zero)]) _ from H)
    cases HE
  · rintro ⟨shared, RA, RN⟩
    rw [EBA] at RA
    rw [EBN] at RN
    obtain ⟨ps, Eps, RP⟩ := (show ScopedCompute _ _
      (ProofShape.mkApps (.const family []) [.forallE assignedRaw (.sort .zero)]) shared from RA).const_spine hinert
    obtain ⟨qs, Eqs, RQ⟩ := (show ScopedCompute _ _
      (ProofShape.mkApps (.const family []) [.forallE nativeRaw (.sort .zero)]) shared from RN).const_spine hinert
    cases RP with
    | cons RP RPnil =>
      cases RPnil
      cases RQ with
      | cons RQ RQnil =>
        cases RQnil
        have Epq := ProofShape.app.inj (Eps.symm.trans Eqs) |>.2
        rw [← Epq] at RQ
        obtain ⟨da, ca, rfl, Rda⟩ := RP.forallE_domain_inv (@erased_joint_union_head _ D)
        obtain ⟨dn, cn, HE, Rdn⟩ := RQ.forallE_domain_inv (@erased_joint_union_head _ D)
        cases HE
        have HA := scoped_normal_fixed Rda (fun Δ =>
          (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
        have HN := scoped_normal_fixed Rdn (fun Δ =>
          (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
        cases HA.symm.trans HN
  · have hP : env.HasType univs (assigned :: context Γ)
        (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
      (IsDefEq.sortDF (by trivial) (by trivial)
        (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
          (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
    have hx := HasType.lam types_equal.hasType.1 hP
    obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, _, _, _, _, _,
      _, hwf, _, Hraw, _⟩ := henv.ordered.projectionShape hi
    obtain ⟨doms, result, hraw, _, _, hhead, _⟩ := Hraw.forallArity
    rw [hraw] at hwf
    obtain ⟨hctx, _, hr⟩ := IsType.wrapForalls_inv henv (by trivial) hwf
    have hresult : result = mkApps (.const fam.name (VLevel.params decl.uvars))
        result.getAppFnArgs.2 := by
      rw [← hhead]
      exact (mkApps_getAppFnArgs_eq result).symm
    rw [hresult] at hr
    obtain ⟨_, hh⟩ := VExpr.WF.of_mkApps henv hctx ⟨_, hr⟩
    obtain ⟨ci, hci, _, hcount⟩ := HasType.const_inv henv hctx hh
    rw [hname, hc] at hci
    cases Option.some.inj hci
    have hl : ([] : List VLevel).length = info.uvars := by
      have hz : decl.uvars = 0 := by simpa using hcount
      simp [← huvars, hz]
    have hctor := HasType.const (Γ := context Γ)
      (henv.ordered.projectionConstructor hi) (by simp : ∀ l ∈ ([] : List VLevel), l.WF univs) hl
    rw [hshape] at hctor
    have hpartial := HasType.app hctor Hparam.hasType.1
    change env.HasType univs (context Γ) _
      (.forallE (.forallE assigned (.sort .zero))
        (.app (.const family []) ((VExpr.forallE assigned (.sort .zero)).lift))) at hpartial
    have hfull := HasType.app hpartial hx
    exact ⟨_, by simpa only [VExpr.inst, VExpr.inst_lift] using hfull⟩
  · intro x y hx hy
    exact ⟨BoxCarrierAlignment.certified_recursive_guard heq hs hD hi hp hf hshape hc hC Hparam HT hx hy,
      BoxCarrierAlignment.certified_recursive_guard heq hs hD hi hp hf hshape hc hC Hparam.symm HT.symm
        (Hbox.defeq hx) (Hbox.defeq hy)⟩

end Lean4Lean.VEnv.Strengthening
