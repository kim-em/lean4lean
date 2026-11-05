import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeForkInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply

/-! # Joining independently selected type-supply histories

Type-rooted fork joining aligns selected Pi exposures. Type-instantiation
joining then aligns their codomains after the same ordinary argument image is
supplied. Induction follows every conversion and application in both histories,
without normalizing either history to a preselected checkpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private spine_head_type spine_function_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply
variable [Params] {D : PureObservation.Definitions}

/-- Under type-only fork joining, two joined typed types remain joined after
independent further computations. The shared raw output is realized as a type
before its fork is used; no confluence assumption on arbitrary data is needed. -/
theorem TypeForkJoin.compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) shared)
    (RU : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ U) shared)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ U) right) :
    ∃ joint, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left joint ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right joint := by
  obtain ⟨l, SL, LL⟩ := HF hΓ hT RT RL
  obtain ⟨r, SR, RR⟩ := HF hΓ hU RU RR
  obtain ⟨S, HS, ES⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RT
  obtain ⟨joint, L, R⟩ := HF hΓ HS.hasType.2 (ES ▸ SL) (ES ▸ SR)
  exact ⟨joint, LL.trans L, RR.trans R⟩

/-- Joined Pi types give joined instantiated codomains even when their written
domains differ. The argument has ordinary typing at both domains. Pi readout
retains the two original binder contexts; HJ instantiates each branch, and a
fork at their realized common type composes the results. -/
theorem TypeForkJoin.pi_inst_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u')) (hE : env.HasType univs (C :: Γ) E (.sort v'))
    (hx : env.HasType univs Γ x A) (hx' : env.HasType univs Γ x C)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) shared)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ C) (proofErase (C :: Γ) E)) shared) :
    ∃ joint, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) joint ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (E.inst x)) joint := by
  obtain ⟨X, Y, ⟨_, _, _, _, _, _, _, RB⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RL
  obtain ⟨_, _, _, _, _, _, _, RE⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hC hE (RR.trans (.beta Rβ))
  obtain ⟨l, LB, LY⟩ := HF.instantiation_join hΓ hA hB hx RB
  obtain ⟨r, RE, RY⟩ := HF.instantiation_join hΓ hC hE hx' RE
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨B', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hB rfl rfl RB
  have HI := HB'.hasType.2.instN henv.ordered Ctx.InstN.zero hx
  have EI : proofErase Γ (B'.inst x) = Y.inst (proofErase Γ x) := by
    rw [proofErase_instN hΓA hx Ctx.InstN.zero HB'.hasType.2, EB']
  obtain ⟨joint, L, R⟩ := HF hΓ HI (EI ▸ LY) (EI ▸ RY)
  exact ⟨joint, LB.trans L, RE.trans R⟩

private theorem selected_pi_assignment
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) (.forallE rawA rawB)) :
    ∃ A B, env.IsType univs Γ A ∧ env.IsType univs (A :: Γ) B ∧
      env.HasType univs Γ f (.forallE A B) ∧
      proofErase Γ A = rawA ∧ proofErase (A :: Γ) B = rawB := by
  obtain ⟨v, hT⟩ := hf.isType henv hΓ
  obtain ⟨P, HP, EP⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl R
  obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv EP
  obtain ⟨hA, hB⟩ := IsType.forallE_inv henv ⟨v, HP.hasType.2⟩
  exact ⟨A, B, hA, hB, HP.defeq hf, EA, EB⟩

private theorem selected_argument_typing
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs Γ (VExpr.mkApps (.app f x) args) S) :
    env.HasType univs Γ x A := by
  obtain ⟨V, hApp⟩ := spine_head_type hΓ ht
  obtain ⟨A₀, B₀, hf₀, hx₀⟩ := hApp.app_inv henv hΓ
  obtain ⟨⟨_, HA⟩, _⟩ := (hf₀.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact HA.defeq hx₀

/-- Every pair of selected application histories from joined assignments of
the same ordinarily typed head has joined final outputs. The argument images
are the same in both histories and may be arbitrary independent computations
of the actual arguments. All pre-application, inter-application and final
conversions are retained. TypeForkJoin is the explicit remaining premise. -/
theorem TypeForkJoin.selected_supply_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T₁) (hf' : env.HasType univs Γ f T₂)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) S)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T₁) shared)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T₂) shared)
    (WL : SelectedPiSupply (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T₁) images left)
    (WR : SelectedPiSupply (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T₂) images right) :
    ∃ joint, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left joint ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right joint := by
  induction args generalizing f T₁ T₂ images shared left right with
  | nil =>
    cases RX
    cases WL with
    | done L =>
      cases WR with
      | done R =>
        exact HF.compute_join heq hs hΓ (hf.isType henv hΓ).choose_spec
          (hf'.isType henv hΓ).choose_spec RL RR L R
  | cons x args ih =>
    change env.HasType univs Γ (VExpr.mkApps (.app f x) args) S at ht
    cases RX with
    | cons RImage RImages =>
      cases WL with
      | @app _ rawA rawB image images _ RPiL WL =>
        cases WR with
        | @app _ rawC rawE _ _ _ RPiR WR =>
          obtain ⟨A, B, hA, hB, hfL, EA, EB⟩ := selected_pi_assignment heq hs hΓ hf RPiL
          obtain ⟨C, E, hC, hE, hfR, EC, EE⟩ := selected_pi_assignment heq hs hΓ hf' RPiR
          obtain ⟨p, LP, RP⟩ := HF.compute_join heq hs hΓ (hf.isType henv hΓ).choose_spec
            (hf'.isType henv hΓ).choose_spec RL RR RPiL RPiR
          have hx := selected_argument_typing hΓ hfL ht
          obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize
            (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RImage
          have hy := HXY.hasType.2
          obtain ⟨⟨_, HAC⟩, _⟩ := (hfL.uniqU henv hΓ hfR).forallE_inv henv hΓ
          have hy' := HAC.defeq hy
          obtain ⟨q, LQ, RQ⟩ := HF.pi_inst_join heq hs hΓ hA.choose_spec hB.choose_spec
            hC.choose_spec hE.choose_spec hy hy' (by simpa only [EA, EB] using LP)
            (by simpa only [EC, EE] using RP)
          have HEf := IsDefEq.appDF hfL HXY
          have HEargs := spine_function_eq hΓ HEf.toU ht
          have ht' := (HEargs.of_l henv hΓ ht).hasType.2
          have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
          have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, hC⟩
          have EIL := proofErase_instN hΓA hy Ctx.InstN.zero hB.choose_spec
          have EIR := proofErase_instN hΓC hy' Ctx.InstN.zero hE.choose_spec
          rw [EB, EY] at EIL
          rw [EE, EY] at EIR
          exact ih (hfL.app hy) (hfR.app hy') ht' RImages LQ RQ
            (by rwa [EIL]) (by rwa [EIR])

end Lean4Lean.VEnv.Strengthening
