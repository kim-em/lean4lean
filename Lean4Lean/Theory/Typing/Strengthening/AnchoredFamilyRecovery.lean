import Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalImage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnchoredCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Selected recovery paths with protected type-family domains

The finite path carries its selected output through terminal typed leaves, neutral
selected-output leaves, and type families whose heads lie outside local binders.
For a function, head exposure returns either a lambda at the selected domain
or a protected neutral domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A path ending in a terminal typed image, a protected neutral output, or a type family.
The cutoff counts local binders; the selected output retains core conversions. -/
inductive AnchoredFamilyRecovery (D : PureObservation.Definitions) :
    Nat → List VExpr → VExpr → ProofShape → Nat → Prop where
  | type : env.HasType univs Γ e (.sort u) → AnchoredFamilyRecovery D cut Γ e (.sort u) 0
  /-- Actual terminal typing excludes function and retained-projection use. -/
  | terminal : TerminalImage Γ e → AnchoredFamilyRecovery D cut Γ e out 0
  /-- A neutral selected output cannot feed a function or structure recovery.
  No native recovery or normalization of the expression is required. -/
  | neutral : AnchoredCarrier cut out → AnchoredFamilyRecovery D cut Γ e out 0
  | family : env.HasType univs Γ e (.forallE A (.sort u)) →
      AnchoredCarrier cut (proofErase Γ A) →
      AnchoredFamilyRecovery D cut Γ e (.forallE (proofErase Γ A) (.sort u)) 0
  | lam : AnchoredFamilyRecovery D (cut + 1) (A :: Γ) b B n →
      AnchoredFamilyRecovery D cut Γ (.lam A b) (.forallE (proofErase Γ A) B) (n + 1)
  | app : AnchoredFamilyRecovery D cut Γ f (.forallE A B) n →
      AnchoredFamilyRecovery D cut Γ (.app f a) (B.inst (proofErase Γ a)) (n + 1)
  | convert : AnchoredFamilyRecovery D cut Γ e T n → Compute (ErasedIotaPrimitive D) T U →
      AnchoredFamilyRecovery D cut Γ e U (n + 1)

/-- Typed substitution preserves both the rank and the exact selected output.
No image recovery is required; the substitution must preserve protected heads. -/
theorem AnchoredFamilyRecovery.subst (H : AnchoredFamilyRecovery D cut Γ e out n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (WH : PreservesCarrierHeads cut cut' τ) :
    AnchoredFamilyRecovery D cut' Γ₀ (e.subst σ) (out.subst τ) n := by
  induction H generalizing Γ₀ σ τ T cut' with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | terminal H => exact .terminal (H.subst hΓ₀ W)
  | neutral HA => exact .neutral (HA.subst WH)
  | family h HA =>
    obtain ⟨_, hPi⟩ := h.isType henv W.wf
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    simp only [ProofShape.subst]
    rw [← proofErase_subst_with hΓ₀ W hA ES]
    exact AnchoredFamilyRecovery.family (by simpa only [VExpr.subst] using (h.subst henv.orderedStrong W hΓ₀)) (by
        simpa only [proofErase_subst_with hΓ₀ W hA ES] using HA.subst WH)
  | @lam cut A Γ b B n H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES] using
      AnchoredFamilyRecovery.lam (ih ⟨hΓ₀, u, hA'⟩ (W.lift henv.ordered hA) ES' hb WH.lift)
  | @app cut Γ f A B n a H ih =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES] using
      AnchoredFamilyRecovery.app (a := a.subst σ) (ih hΓ₀ W ES hf WH)
  | convert H R ih =>
    exact .convert (ih hΓ₀ W ES ht WH) (R.subst (fun H => erased_iota_primitive_subst H))

private theorem core_forall_parts
    (R : Compute (ErasedIotaPrimitive D) (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute (ErasedIotaPrimitive D) A A' ∧
      Compute (ErasedIotaPrimitive D) B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (E ▸ erased_iota_primitive_head H).elim
  | beta H =>
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts (E ▸ H)
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA, HB⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA', HB'⟩ := ih₂ rfl
    exact ⟨_, _, HE, HA.trans HA', HB.trans HB'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | app | proj | lam => cases E

/-- Core computation preserves a protected selected output. -/
theorem ProofShape.AnchoredCarrier.core_compute
    (H : AnchoredCarrier cut A) (R : Compute (ErasedIotaPrimitive D) A B) :
    AnchoredCarrier cut B := by
  have RC : ScopedCompute (ErasedJointStage D 0) [] A B := R.scoped (fun H => .base H)
  exact H.compute (erased_joint_stage_head 0) RC

/-- Head exposure either stops at terminal typing or a protected neutral output,
or retains computation from a family/exposed Pi to the selected output.
Application consumes a smaller body path and one conversion node;
the rank remains strictly below the original application path. -/
theorem AnchoredFamilyRecovery.expose (H : AnchoredFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    TerminalImage Γ e ∨ AnchoredCarrier cut out ∨
      (∃ C u, env.HasType univs Γ e (.forallE C (.sort u)) ∧
        AnchoredCarrier cut (proofErase Γ C) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ C) (.sort u)) out) ∨
      ∃ A b B m, m < n ∧ AnchoredFamilyRecovery D (cut + 1) (A :: Γ) b B m ∧
        VExpr.BetaRed e (.lam A b) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) B) out := by
  induction n using Nat.strongRecOn generalizing cut Γ e out T with
  | ind n ih =>
    cases H with
    | type h => exact .inl (.type h)
    | terminal H => exact .inl H
    | neutral HA => exact .inr (.inl HA)
    | family h HA => exact .inr (.inr (.inl ⟨_, _, h, HA, .refl⟩))
    | lam H => exact .inr (.inr (.inr ⟨_, _, _, _, by omega, H, .refl, .refl⟩))
    | @convert cut Γ e source k out H R =>
      rcases ih k (by omega) H hΓ ht with HS | HN | ⟨C, u, hf, HA, RT⟩ | ⟨A, b, B, m, hm, HB, RB, RT⟩
      · exact .inl HS
      · exact .inr (.inl (HN.core_compute R))
      · exact .inr (.inr (.inl ⟨C, u, hf, HA, RT.trans R⟩))
      · exact .inr (.inr (.inr ⟨A, b, B, m, by omega, HB, RB, RT.trans R⟩))
    | @app cut Γ f X Y k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓ hf with HT | HN | ⟨C, u, hfPi, _, _⟩ | ⟨A, b, B, m, hm, HB, RF, RT⟩
      · exact (HT.not_function hΓ hf).elim
      · exact (HN.not_exposed .function).elim
      · have hxC := argument_at_displayed_domain hΓ hf hfPi hx
        exact .inl (.type (by simpa only [VExpr.inst] using HasType.app hfPi hxC))
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
      have Hinst : AnchoredFamilyRecovery D cut Γ (b.inst a) (B.inst (proofErase Γ a)) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using HB.subst hΓ WS ES hb (PreservesCarrierHeads.one (proofErase Γ a))
      have RBinst : Compute (ErasedIotaPrimitive D) (B.inst (proofErase Γ a))
          (Y.inst (proofErase Γ a)) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst
          (σ := ProofShape.Subst.one (proofErase Γ a)) (fun H => erased_iota_primitive_subst H)
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih (m + 1) (by omega) (Hinst.convert RBinst) hΓ HE'.hasType.2 with
        HT | HN | ⟨C, u, hfFamily, HC, RT'⟩ | ⟨C, body, B', j, hj, Hbody, RB', RT'⟩
      · exact .inl (HT.back hΓ HE')
      · exact .inr (.inl HN)
      · exact .inr (.inr (.inl ⟨C, u, (HE'.toU.of_r henv hΓ hfFamily).hasType.1, HC, RT'⟩))
      · exact .inr (.inr (.inr ⟨C, body, B', j, by omega, Hbody, R.trans RB', RT'⟩))


/-- Every old sort-rooted path embeds at any cutoff, so the new invariant
extends the previously checked fragment without weakening its certificates. -/
theorem SortRootedRecovery.anchored (H : SortRootedRecovery D Γ e out n) :
    AnchoredFamilyRecovery D cut Γ e out n := by
  induction H generalizing cut with
  | type h => exact .type h
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih
  | convert _ R ih => exact .convert ih R

/-- A retained function with selected Pi output either computes to a lambda
at that exact domain or the selected domain has a protected variable head.
No common reduct of native and assigned lambda annotations is assumed. -/
theorem AnchoredFamilyRecovery.selected_domain_or_anchored
    (H : AnchoredFamilyRecovery D cut Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C E))
    (hn : ¬ IsProof Γ f) :
    (∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam A body)) ∨ AnchoredCarrier cut A := by
  rcases H.expose hΓ hf with HT | HN | ⟨X, u, _, HX, RT⟩ | ⟨X, b, Y, _, _, _, RF, RT⟩
  · exact (HT.not_function hΓ hf).elim
  · exact (HN.not_exposed .function).elim
  · obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have RC : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ X) A :=
      RA.scoped (fun H => .base H)
    exact .inr (HX.compute (erased_joint_stage_head 0) RC)
  · obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
    have hn' := mt (isProof_congr hΓ HE).2 hn
    have RB := proofErase_beta_forward hΓ hf RF
    rw [show proofErase Γ (.lam X b) = .lam _ _ from if_neg hn'] at RB
    exact .inl ⟨_, (ScopedCompute.beta RB).trans
      (.lam (RA.scoped (fun H => .base H)) .refl)⟩

/-- The selected-path result supplies precisely the computed or inert cases
of the enlarged recursive transport theorem at stage zero. -/
theorem AnchoredFamilyRecovery.selected_domain_or_inert
    (H : AnchoredFamilyRecovery D cut Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C E))
    (hn : ¬ IsProof Γ f) :
    (∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam A body)) ∨
    (∀ {out}, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) A out →
      ¬ CarrierExposure out) := by
  rcases H.selected_domain_or_anchored hΓ hf hn with HC | HA
  · exact .inl HC
  · exact .inr (HA.inert (erased_joint_stage_head 0))

/-- Any type family at a neutral assigned domain supplies the new leaf at
its actual assigned Pi erasure. The function need not expose a lambda with
that annotation, and may be typed there by conversion. -/
theorem AnchoredFamilyRecovery.of_family
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A (.sort u)))
    (HA : AnchoredCarrier cut (proofErase Γ A)) :
    AnchoredFamilyRecovery D cut Γ f (proofErase Γ (.forallE A (.sort u))) 0 := by
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨w, hA⟩, _, hU⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  rw [show proofErase Γ (.forallE A (.sort u)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi),
    show proofErase (A :: Γ) (.sort u) = .sort u from
      if_neg (not_isProof_of_sort hΓA hU)]
  exact .family hf HA

end Lean4Lean.VEnv.Strengthening
