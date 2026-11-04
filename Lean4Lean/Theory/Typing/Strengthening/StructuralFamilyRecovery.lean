import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralFunctionCarrierConversion

/-! # Selected recovery with convertible structural family domains

A structural family leaf retains its beta-exposed lambda. Applications of the
family are types, so exposure terminates there even when assigned and written
function domains have no exact recovery join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts
  from Lean4Lean.Theory.Typing.Strengthening.AnchoredFamilyRecovery
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

omit [Params] in
private theorem beta_subst (H : VExpr.BetaRed e out) :
    VExpr.BetaRed (e.subst σ) (out.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | beta => rw [VExpr.subst_inst]; exact .beta

/-- A path ending in a type, a protected neutral output, or a type family
with a neutral or convertible structural domain.
The cutoff counts local binders; the selected output retains core conversions. -/
inductive StructuralFamilyRecovery (D : PureObservation.Definitions) :
    Nat → List VExpr → VExpr → ProofShape → Nat → Prop where
  | type : env.HasType univs Γ e (.sort u) → StructuralFamilyRecovery D cut Γ e (.sort u) 0
  /-- A neutral selected output cannot feed a function or structure recovery.
  No native recovery or normalization of the expression is required. -/
  | neutral : AnchoredCarrier cut out → StructuralFamilyRecovery D cut Γ e out 0
  | family : env.HasType univs Γ e (.forallE A (.sort u)) →
      AnchoredCarrier cut (proofErase Γ A) →
      StructuralFamilyRecovery D cut Γ e (.forallE (proofErase Γ A) (.sort u)) 0
  /-- A sort-valued function at a structural function domain may expose a
  lambda at another domain. Equality of these domains follows from typing;
  the protected inner source domain supports whole-guard conversion. -/
  | structural : env.HasType univs Γ e (.forallE (.forallE A (.sort v)) (.sort u)) →
      AnchoredCarrier cut (proofErase Γ A) →
      VExpr.BetaRed e (.lam (.forallE B (.sort v)) b) →
      StructuralFamilyRecovery D cut Γ e
        (.forallE (.forallE (proofErase Γ A) (.sort v)) (.sort u)) 0
  | lam : StructuralFamilyRecovery D (cut + 1) (A :: Γ) b B n →
      StructuralFamilyRecovery D cut Γ (.lam A b) (.forallE (proofErase Γ A) B) (n + 1)
  | app : StructuralFamilyRecovery D cut Γ f (.forallE A B) n →
      StructuralFamilyRecovery D cut Γ (.app f a) (B.inst (proofErase Γ a)) (n + 1)
  | convert : StructuralFamilyRecovery D cut Γ e T n → Compute (ErasedIotaPrimitive D) T U →
      StructuralFamilyRecovery D cut Γ e U (n + 1)

/-- Typed substitution preserves both the rank and the exact selected output.
No image recovery is required; the substitution must preserve protected heads. -/
theorem StructuralFamilyRecovery.subst (H : StructuralFamilyRecovery D cut Γ e out n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (WH : PreservesCarrierHeads cut cut' τ) :
    StructuralFamilyRecovery D cut' Γ₀ (e.subst σ) (out.subst τ) n := by
  induction H generalizing Γ₀ σ τ T cut' with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | neutral HA => exact .neutral (HA.subst WH)
  | family h HA =>
    obtain ⟨_, hPi⟩ := h.isType henv W.wf
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    simp only [ProofShape.subst]
    rw [← proofErase_subst_with hΓ₀ W hA ES]
    exact StructuralFamilyRecovery.family (by simpa only [VExpr.subst] using (h.subst henv.orderedStrong W hΓ₀)) (by
        simpa only [proofErase_subst_with hΓ₀ W hA ES] using HA.subst WH)
  | @structural Γ e A v u cut B b h HA R =>
    obtain ⟨_, hPi⟩ := h.isType henv W.wf
    obtain ⟨⟨_, hK⟩, _, _⟩ := hPi.forallE_inv henv
    obtain ⟨⟨_, hA⟩, _, _⟩ := hK.forallE_inv henv
    simp only [ProofShape.subst]
    rw [← proofErase_subst_with hΓ₀ W hA ES]
    apply StructuralFamilyRecovery.structural (B := B.subst σ) (b := b.subst σ.lift)
      (by simpa only [VExpr.subst] using h.subst henv.orderedStrong W hΓ₀)
      (by simpa only [proofErase_subst_with hΓ₀ W hA ES] using HA.subst WH)
    simpa only [VExpr.subst] using beta_subst (σ := σ) R
  | @lam cut A Γ b B n H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES] using
      StructuralFamilyRecovery.lam (ih ⟨hΓ₀, u, hA'⟩ (W.lift henv.ordered hA) ES' hb WH.lift)
  | @app cut Γ f A B n a H ih =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES] using
      StructuralFamilyRecovery.app (a := a.subst σ) (ih hΓ₀ W ES hf WH)
  | convert H R ih =>
    exact .convert (ih hΓ₀ W ES ht WH) (R.subst (fun H => erased_iota_primitive_subst H))

/-- Head exposure either stops at type typing or a protected neutral output,
or retains computation from a family/exposed Pi to the selected output.
Application consumes a smaller body path and one conversion node;
the rank remains strictly below the original application path. -/
theorem StructuralFamilyRecovery.expose (H : StructuralFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    env.IsType univs Γ e ∨ AnchoredCarrier cut out ∨
      (∃ C u, env.HasType univs Γ e (.forallE C (.sort u)) ∧
        AnchoredCarrier cut (proofErase Γ C) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ C) (.sort u)) out) ∨
      (∃ A B b u v, env.HasType univs Γ e (.forallE (.forallE A (.sort v)) (.sort u)) ∧
        AnchoredCarrier cut (proofErase Γ A) ∧
        VExpr.BetaRed e (.lam (.forallE B (.sort v)) b) ∧
        Compute (ErasedIotaPrimitive D)
          (.forallE (.forallE (proofErase Γ A) (.sort v)) (.sort u)) out) ∨
      ∃ A b B m, m < n ∧ StructuralFamilyRecovery D (cut + 1) (A :: Γ) b B m ∧
        VExpr.BetaRed e (.lam A b) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) B) out := by
  induction n using Nat.strongRecOn generalizing cut Γ e out T with
  | ind n ih =>
    cases H with
    | type h => exact .inl ⟨_, h⟩
    | neutral HA => exact .inr (.inl HA)
    | family h HA => exact .inr (.inr (.inl ⟨_, _, h, HA, .refl⟩))
    | structural h HA R => exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, h, HA, R, .refl⟩)))
    | lam H => exact .inr (.inr (.inr (.inr ⟨_, _, _, _, by omega, H, .refl, .refl⟩)))
    | @convert cut Γ e source k out H R =>
      rcases ih k (by omega) H hΓ ht with HS | HN | ⟨C, u, hf, HA, RT⟩ | ⟨X, Y, b, u, v, hf, HA, RF, RT⟩ | ⟨A, b, B, m, hm, HB, RB, RT⟩
      · exact .inl HS
      · exact .inr (.inl (HN.core_compute R))
      · exact .inr (.inr (.inl ⟨C, u, hf, HA, RT.trans R⟩))
      · exact .inr (.inr (.inr (.inl ⟨X, Y, b, u, v, hf, HA, RF, RT.trans R⟩)))
      · exact .inr (.inr (.inr (.inr ⟨A, b, B, m, by omega, HB, RB, RT.trans R⟩)))
    | @app cut Γ f X Y k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓ hf with ⟨_, hs⟩ | HN | ⟨C, u, hfPi, _, _⟩ | ⟨X, Y, b, u, v, hfStruct, _, _, _⟩ | ⟨A, b, B, m, hm, HB, RF, RT⟩
      · exact ((hs.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
      · exact (HN.not_exposed .function).elim
      · have hxC := argument_at_displayed_domain hΓ hf hfPi hx
        exact .inl ⟨u, by simpa only [VExpr.inst] using HasType.app hfPi hxC⟩
      · have hxK := argument_at_displayed_domain hΓ hf hfStruct hx
        exact .inl ⟨u, by simpa only [VExpr.inst] using HasType.app hfStruct hxK⟩
      obtain ⟨_, _, EE, _, RB⟩ := core_forall_parts RT
      obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
      have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
      obtain ⟨⟨u, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
      have hfPi := (HE.toU.of_r henv hΓ (HasType.lam hA hb)).hasType.1
      have hxA := argument_at_displayed_domain hΓ hf hfPi hx
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have WS := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA hxA
      have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one a)
          (ProofShape.Subst.one (proofErase Γ a)) := erasedSubstAgreement_one hΓA hxA
      have Hinst : StructuralFamilyRecovery D cut Γ (b.inst a) (B.inst (proofErase Γ a)) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using HB.subst hΓ WS ES hb (PreservesCarrierHeads.one (proofErase Γ a))
      have RBinst : Compute (ErasedIotaPrimitive D) (B.inst (proofErase Γ a))
          (Y.inst (proofErase Γ a)) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst
          (σ := ProofShape.Subst.one (proofErase Γ a)) (fun H => erased_iota_primitive_subst H)
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih (m + 1) (by omega) (Hinst.convert RBinst) hΓ HE'.hasType.2 with
        ⟨v, hv⟩ | HN | ⟨C, u, hfFamily, HC, RT'⟩ | ⟨X, Y, b, u, v, hfStruct, HA, RF, RT'⟩ | ⟨C, body, B', j, hj, Hbody, RB', RT'⟩
      · exact .inl ⟨v, (HE'.toU.of_r henv hΓ hv).hasType.1⟩
      · exact .inr (.inl HN)
      · exact .inr (.inr (.inl ⟨C, u, (HE'.toU.of_r henv hΓ hfFamily).hasType.1, HC, RT'⟩))
      · exact .inr (.inr (.inr (.inl ⟨X, Y, b, u, v,
          (HE'.toU.of_r henv hΓ hfStruct).hasType.1, HA, R.trans RF, RT'⟩)))
      · exact .inr (.inr (.inr (.inr ⟨C, body, B', j, by omega, Hbody, R.trans RB', RT'⟩)))



/-- Every earlier structural-family path embeds without changing its rank. -/
theorem AnchoredFamilyRecovery.structural (H : AnchoredFamilyRecovery D cut Γ e out n) :
    StructuralFamilyRecovery D cut Γ e out n := by
  induction H with
  | type h => exact .type h
  | neutral h => exact .neutral h
  | family h HA => exact .family h HA
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih
  | convert _ R ih => exact .convert ih R

private theorem erase_function_sort
    (hΓ : OnCtx Γ (env.IsType univs))
    (hK : env.HasType univs Γ (.forallE A (.sort v)) (.sort w)) :
    proofErase Γ (.forallE A (.sort v)) = .forallE (proofErase Γ A) (.sort v) := by
  obtain ⟨⟨u, hA⟩, _, hv⟩ := hK.forallE_inv henv
  rw [show proofErase Γ (.forallE A (.sort v)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hK),
    show proofErase (A :: Γ) (.sort v) = .sort v from
      if_neg (not_isProof_of_sort (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hv)]

/-- The selected recovery path repairs an application from its existing finite
argument guard. A structural-family leaf converts the whole guard to the
written domain; the other leaves use exact exposure or neutral inertness.
No target comparison or guard beyond the recursive premises is assumed. -/
theorem StructuralFamilyRecovery.application
    (hs : D.Sound env univs)
    (H : StructuralFamilyRecovery D cut Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      A (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  rcases H.expose hΓ hf with ⟨_, hsort⟩ | HN | ⟨X, u, _, HA, RT⟩ |
      ⟨X, Y, b, u, v, hstruct, HA, RF, RT⟩ | ⟨X, b, Y, _, _, _, RF, RT⟩
  · exact ((hsort.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  · exact (HN.not_exposed .function).elim
  · obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have HAA := HA.core_compute RA
    exact .app HF (HX.checked_of_no_exposure (HAA.inert (erased_joint_stage_head 0)))
  · obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have RDA : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
        (.forallE (proofErase Γ X) (.sort v)) _ := RA.scoped (fun H => .base H)
    have HX₀ := ComputedJointCheck.carrierCompute RDA HX
    have hx₀ := argument_at_displayed_domain hΓ hf hstruct hx
    have hy₀ := argument_at_displayed_domain hΓ hf hstruct hy
    have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hstruct
    obtain ⟨⟨_, hY⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HU := HE.hasType.2.uniqU henv hΓ (HasType.lam hY hb)
    obtain ⟨⟨_, HXY⟩, _, _⟩ := HU.forallE_inv henv hΓ
    obtain ⟨⟨_, HXY⟩, _, _⟩ := HXY.toU.forallE_inv henv hΓ
    obtain ⟨_, hPi⟩ := hstruct.isType henv hΓ
    obtain ⟨⟨_, hX⟩, _, _⟩ := hPi.forallE_inv henv
    obtain ⟨⟨w, hXX⟩, _, hv⟩ := hX.forallE_inv henv
    have EV : proofErase (X :: Γ) (.sort v) = .sort v :=
      if_neg (not_isProof_of_sort (Γ := X :: Γ) ⟨hΓ, w, hXX⟩ hv)
    have HA₀ : AnchoredCarrier 0 (proofErase Γ X) := by
      obtain ⟨i, args, _, EE⟩ := HA
      exact ⟨i, args, by omega, EE⟩
    have HC := proofErase_computed_joint_dependent_neutral_function_carrier_convert hs hΓ HXY HA₀ hx₀ hy₀
      (by simpa only [EV] using HX₀)
    rw [EV] at HC
    have hn' := mt (isProof_congr hΓ HE).2 hn
    have RB := proofErase_beta_forward hΓ hstruct RF
    rw [show proofErase Γ (.lam (.forallE Y (.sort v)) b) = .lam _ _ from if_neg hn',
      erase_function_sort hΓ hY] at RB
    exact .appComputed (.beta RB) HF HC
  · obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
    have hn' := mt (isProof_congr hΓ HE).2 hn
    have RB := proofErase_beta_forward hΓ hf RF
    rw [show proofErase Γ (.lam X b) = .lam _ _ from if_neg hn'] at RB
    exact .appComputed ((ScopedCompute.beta RB).trans
      (.lam (RA.scoped (fun H => .base H)) .refl)) HF HX

/-- A beta-exposed structural family carries its exact assigned erasure,
without requiring that the written and assigned inner domains compute to a
common annotation. -/
theorem StructuralFamilyRecovery.of_structural
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (.forallE A (.sort v)) (.sort u)))
    (HA : AnchoredCarrier cut (proofErase Γ A))
    (R : VExpr.BetaRed f (.lam (.forallE B (.sort v)) b)) :
    StructuralFamilyRecovery D cut Γ f
      (proofErase Γ (.forallE (.forallE A (.sort v)) (.sort u))) 0 := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hK⟩, _, _⟩ := hPi.forallE_inv henv
  rw [erase_function_sort hΓ hPi, erase_function_sort hΓ hK]
  exact .structural hf HA R

end Lean4Lean.VEnv.Strengthening
