import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaRoot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializedReadout

/-! # Read a specialized Eq guard under the fresh eta binder

The specialized root requires five arguments, forcing the eta body to complete
a four-argument prefix. Its component guard descends below the ambient unused
binders before its semantic equation is instantiated at the original endpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

private theorem computed_prefix_length
    (H : ComputedJointPrefixPrimitive Step Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) out) :
    args.length = 5 := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec ls) args = source at H
  cases H with
  | @intro α a b v w M minor HG =>
    obtain ⟨_, _, rfl⟩ := ProofShape.const_spine_inj (ps' := [α,a,M,minor,b]) (ls' := [v,w]) ES
    rfl

/-- A specialized computed Eq root inside a computed fresh eta body forces
the original completion's endpoint equation. Arity supplies the full fresh
five-argument probe; only the reflected semantic equation is specialized. -/
theorem pi_inert_eq_computed_fresh_eta_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) (.forallE A B))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (Eargs : pre ++ x :: pending = [α,a,M,minor,b])
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage)
        (proofEraseCtx (A.liftN count offset :: Γ')))
      ((((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ [etaArgument u])
      (bodyPre ++ bodyPending))
    (HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
      (proofEraseCtx (A.liftN count offset :: Γ'))
      (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target) :
    env.IsDefEq univs Γ a b α := by
  have hbodyLen := computed_prefix_length HQ
  have hlen := HA.length_eq
  have hcomplete := congrArg List.length Eargs
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen hcomplete
  have hfour : pre.length = 4 := by omega
  have Etake := congrArg (List.take 4) Eargs
  have EP : (pre ++ x :: pending).take 4 = pre := by rw [← hfour, List.take_left]
  simp only [EP, List.take_succ_cons, List.take_zero] at Etake
  subst pre
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at Eargs
  obtain ⟨rfl, rfl⟩ := Eargs
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
    ⟨hΓ', u, hA.weakN henv W⟩
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v,w]) [α,a,M,minor]).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hbody : env.HasType univs (A :: Γ)
      (eqRecBeforeMajor v w α.lift a.lift M.lift minor.lift (.bvar 0)) B := by
    simpa only [eqRecBeforeMajor, VExpr.mkApps, VExpr.lift, VExpr.liftN,
      List.foldl_cons, List.foldl_nil, VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  obtain ⟨_, _, hα, ha, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eextend {e F} (he : env.HasType univs Γ e F) :
      (proofErase (A :: Γ) e.lift).liftN count (offset+1) =
        ((proofErase Γ e).liftN count offset).liftN 1 := by
    rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one he]
    exact (ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _)).symm
  have Efresh : (proofErase (A :: Γ) (.bvar 0)).liftN count (offset+1) = etaArgument u := by
    rw [proofErase_fresh_argument hΓ hA, etaArgument_liftN]
  have HQ' := HQ.mono (erased_static_structure_eta_expansion_stage_mono (Nat.le_max_right bodyStage rootStage))
  have HA' := HA.imp (fun _ _ R => R.mono (fun H =>
    erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left bodyStage rootStage) H.1))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at HA'
  have HG := HQ'.spine_component_guard HA'
  have HG' : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D (max bodyStage rootStage))
      (proofEraseCtx (A.liftN count offset :: Γ'))
      ((proofErase (A :: Γ) α.lift).liftN count (offset+1))
      ((proofErase (A :: Γ) a.lift).liftN count (offset+1))
      ((proofErase (A :: Γ) (.bvar 0)).liftN count (offset+1)) := by
    simpa only [Eextend hα, Eextend ha, Efresh] using HG
  have hd : ErasedScopedPrimitiveCertificateDescent
      (ErasedStaticStructureEtaExpansionStage D (max bodyStage rootStage))
      (ErasedStaticStructureEtaExpansionStage D (max bodyStage rootStage)) :=
    erased_static_structure_eta_expansion_stage_certificate_descent heq hs (max bodyStage rootStage)
  have HP : EqPrefixSpecialization Γ Γ v w v w [α,a,M,minor,x] [α,a,M,minor] := by
    simpa only [List.take_succ_cons, List.take_zero] using
      (EqPrefixSpecialization.of_typed hΓ ht).take 4
  have HF : EqPrefixSpecialization (A :: Γ) Γ v w v w [α,a,M,minor,x]
      [α.lift,a.lift,M.lift,minor.lift,.bvar 0] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      HP.eta hΓ ht hA hf (by change 4 < 5; decide)
  exact HF.read_carrier_guard heq hd hΓA hΓA' W.succ hΓ ht hbody HG'

end Lean4Lean.VEnv.Strengthening
