import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIndexedControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Computation of context-indexed Pi payload observations

The generic payload laws separate ordinary substitution of temporary controls
from component computation. All static structure/function-eta stages preserve
the surrounding typed control program, including changed control annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.IndexedControlObservation
open private erase_app_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- The payload-specific component law. The actual Pi components are typed in
their current context, while the original context remains below the temporary
prefix. Codomains need not be lifts of expressions in that original context. -/
def IndexedPiComponentClosure
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Γ : List VExpr)
    (P : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ' n A B u v X Y}, OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' →
    env.HasType univs Γ' A (.sort u) → env.HasType univs (A :: Γ') B (.sort v) →
    P n (proofEraseCtx Γ') (proofErase Γ' A) (proofErase (A :: Γ') B) →
    ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' A) X →
    ScopedCompute Step (proofEraseCtx (A :: Γ')) (proofErase (A :: Γ') B) Y →
    P n (proofEraseCtx Γ') X Y

/-- Every enriched primitive preserves the indexed observation. Payload
substitution handles newly introduced control binders; structure eta is ruled
out by the closed control type of the observed node. -/
theorem erased_static_structure_stage_indexedControlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hP : PayloadSubstitution P) : ∀ stage {Δ a b n S t o},
    ErasedStaticStructureEtaExpansionStage D stage Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b n S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion hP
  | succ stage ih =>
    intro Δ a b n S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta hP (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure (erased_static_structure_eta_expansion_stage_descent heq hs stage) R).elim

/-- The same control transport works at unbounded finite guard depth. -/
theorem erased_static_structure_union_indexedControlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hP : PayloadSubstitution P)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b) (H : Obs P n Δ S a t o) :
    Obs P n Δ S b t o := by
  obtain ⟨stage, R⟩ := R
  exact erased_static_structure_stage_indexedControlObservation heq hs hP stage R H

/-- Compatible computation preserves typed marked observations when literal
Pi components preserve their histories below every temporary binder prefix.
Free control valuations retain ordinary typing; lambda annotation changes are
handled by identity context substitution after the body has computed. -/
theorem proofErase_scoped_compute_indexedControlObservation
    (hP : PayloadSubstitution P)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S t o}, Step Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o)
    (hpi : IndexedPiComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : S.Typed Δ) (H : Obs P n Δ S source t o) : Obs P n Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S t o e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward hP HS
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    cases H with
    | app _ HF HX =>
      exact .app HT (ihf hΓ' W hf EΓ Ef HS HF)
        (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ'
    have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
    have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
    have EΓA : proofEraseCtx (A :: Γ') = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ', A, hΓ', EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ' hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ') (A' :: Γ') := .succ (.refl hΓ') HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      have HX := HL.lam_parts.2
      apply Obs.lam HT HK
      exact (ihb hΓA W' hb EΓA Eb (HS.cons HX SD) HB).context hP WC
  | @forallE Δ X X' Y Y' RA RB =>
    have HT := H.typing.compute hstep (.forallE RA RB)
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, v, hB⟩ := ht.forallE_inv henv
    cases H with
    | payload _ HP =>
      apply Obs.payload HT
      have HP' : P n (proofEraseCtx Γ') (proofErase Γ' A) (proofErase (A :: Γ') B) := by
        simpa only [EΓ, EA, EB] using HP
      have RA' := EΓ ▸ (EA ▸ RA)
      have RB' : ScopedCompute Step (proofEraseCtx (A :: Γ')) (proofErase (A :: Γ') B) Y' := by
        simpa only [proofEraseCtx, EΓ, EA, EB] using RB
      simpa only [EΓ] using hpi hΓ' W hA hB HP' RA' RB'

end Lean4Lean.VEnv.Strengthening
