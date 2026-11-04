import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Sort readout through full structure and function eta -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.SortControlObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Full structure/function-eta primitives preserve a marked sort demand.
Universe conversion transports its level certificate; the typed control
assignment excludes root structure expansion and sort-valued function eta. -/
theorem erased_static_structure_stage_sortObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HP : ∀ {u v}, P u → u ≈ v → v.WF univs → P v) : ∀ stage {Δ a b n S t o},
    ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      Obs P n Δ S a t o → Obs P n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b n S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort HE hw =>
        have HT := H.typing.compute (Step := fun _ => LevelPrimitive univs)
          erased_level_primitive_descent (.base (.sort HE hw))
        cases H with
        | payload _ hP => exact .payload HT (HP hP HE hw)
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b n S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) R).elim

/-- A finite guard bound is enough for every primitive in the full union. -/
theorem erased_static_structure_union_sortObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HP : ∀ {u v}, P u → u ≈ v → v.WF univs → P v)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b)
    (H : Obs P n Δ S a t o) : Obs P n Δ S b t o := by
  obtain ⟨stage, R⟩ := R
  exact erased_static_structure_stage_sortObservation heq hs HP stage R H

/-- Compatible computation preserves the typed marked universe. Lambda
annotation changes use ordinary context conversion, without native images. -/
theorem proofErase_scoped_compute_sortObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S t o}, Step Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : S.Typed Δ) (H : Obs P n Δ S source t o) : Obs P n Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S t o e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward HS
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' HE.hasType.2 EΓ EE HS (ih₁ hΓ' ht EΓ Ee HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    cases H with
    | app _ HF HX =>
      exact .app HT (ihf hΓ' hf EΓ Ef HS HF)
        (fun key hk => ihx hΓ' hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ'
    have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
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
      exact (ihb hΓA hb EΓA Eb (HS.cons HX SD) HB).context WC
  | forallE => exact H.not_forallE.elim

/-- Every full structure/function-eta computation from a well-formed universe
has a beta readout at an equivalent well-formed universe. Temporary constant
and identity frames, all guard depths and changed annotations are permitted. -/
theorem proofErase_static_structure_union_sort_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.sort u) out) :
    ∃ v, u ≈ v ∧ v.WF univs ∧ BetaRed out (.sort v) := by
  have ht : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort hu
  have E : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ ht)
  have HC : ControlTyping (proofEraseCtx Γ) (.sort u) (.sort (.succ u)) := ⟨Γ, _, hΓ, rfl, ht, E⟩
  have H : Obs (fun v => u ≈ v ∧ v.WF univs) 0 (proofEraseCtx Γ)
      (fun _ _ _ => False) (.sort u) (.sort (.succ u)) .sort :=
    .payload HC ⟨rfl, hu⟩
  have HO := proofErase_scoped_compute_sortObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_sortObservation heq hs (fun H HE hw => ⟨H.1.trans HE, hw⟩))
    R hΓ ht rfl E (fun _ _ _ h => h.elim) H
  obtain ⟨v, ⟨HE, hw⟩, RB⟩ := HO.readout
  exact ⟨v, HE, hw, RB⟩

/-- Common native recovery against an assigned universe yields a literal
native sort. The shared output need not already display a sort or have a native
certificate of its own. Only beta cleanup is appended to the source recovery. -/
theorem static_structure_native_sort_of_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.sort u) shared) :
    ∃ v, u ≈ v ∧ env.HasType univs Γ e (.sort v) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) (.sort v) := by
  obtain ⟨_, hU⟩ := ht.isType henv hΓ
  obtain ⟨v, HE, _, RB⟩ := proofErase_static_structure_union_sort_readout heq hs hΓ
    (hU.sort_inv henv.ordered) RC
  have R := RN.convert (.beta RB)
  obtain ⟨A, hA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht R
  have E : A = .sort v := by
    cases A <;> simp only [proofErase] at EA <;> split at EA <;> cases EA <;> rfl
  exact ⟨v, HE, E ▸ hA, R⟩

end Lean4Lean.VEnv.Strengthening
