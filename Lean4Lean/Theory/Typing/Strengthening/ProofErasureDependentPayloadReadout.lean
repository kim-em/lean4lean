import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentPayloadTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureTypeArgumentOrigin

/-! # Full readout of type payloads across arbitrary discarded arguments

Dependent profiles allow arbitrary data and proof inputs to control frames.
The original type payload still has a lower forward history, and every output
beta-reads that history. Constant cuts need only ordinary whole-root typing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DependentPayloadObservation
open DemandProfile (Profile Typing Fits)
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

private theorem sort_profile (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.sort u)) : Fits Γ (.sort u) .sort := by
  obtain ⟨v, hS⟩ := ht.isType henv hΓ
  exact ⟨⟨v, hS⟩, u, hS.toU⟩

/-- A finite dependent-profile observation reads a computed representative
of its original type payload after every full-union continuation. Ignored
inputs may be arbitrary data or proofs. The observation is a supplied invariant,
not an assertion that every dependent beta body admits such an observation. -/
theorem static_structure_dependent_payload_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v))
    (H : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ e) .sort .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧ BetaRed out (proofErase Γ A') := by
  have HO := proofErase_scoped_compute_dependentPayloadObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_dependent_payload_control heq hs)
    (typeArgumentOrigin_closure (erased_static_structure_eta_expansion_union_certificate_descent heq hs) hΓ)
    R hΓ (Ctx.LiftN.zero []) ht rfl rfl (by intro _ _ _ H; exact H.elim) H
  have HR := HO.realizes
    (show PiOriginObservation.FixedTail 0 0 ProofShape.Subst.id from fun _ => rfl)
    (fun _ _ _ H => H.elim)
  simp only [ProofShape.subst_id, Realizes, ProofShape.liftN_zero] at HR
  obtain ⟨_, ⟨A', HA', rfl, RA⟩, RB⟩ := HR
  exact ⟨A', HA', RA, RB⟩

/-- A constant type-valued cut discards an arbitrary ordinary argument through
its entire computation history. Neither its domain nor the argument needs a
sort-shaped profile or native certificate. Proof arguments are allowed. The
final output has a pure-beta path to a forward computation of the lower body. -/
theorem static_structure_constant_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hb : env.HasType univs Γ b (.sort v)) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b.lift) x)) out) :
    ∃ b', env.IsDefEq univs Γ b b' (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ b) (proofErase Γ b') ∧ BetaRed out (proofErase Γ b') := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hbL : env.HasType univs (A :: Γ) b.lift (.sort v) := hb.weak henv.ordered
  have hf := HasType.lam hA hbL
  have ht : env.HasType univs Γ (.app (.lam A b.lift) x) (.sort v) := hf.app hx
  obtain ⟨w, hPi⟩ := hf.isType henv hΓ
  have HP : Fits Γ (.forallE A (.sort v)) (.arrow .ignored .sort) :=
    ⟨⟨w, hPi⟩, A, .sort v, hPi.toU, ⟨u, hA⟩, sort_profile hΓA hbL⟩
  have EF : proofErase Γ (.lam A b.lift) =
      .lam (proofErase Γ A) ((proofErase Γ b).liftN 1) := by
    rw [show proofErase Γ (.lam A b.lift) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf), proofErase_liftN hΓ hΓA Ctx.LiftN.one hb]
  have EE : proofErase Γ (.app (.lam A b.lift) x) =
      .app (proofErase Γ (.lam A b.lift)) (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HB : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ b v)
      1 (proofEraseCtx (A :: Γ)) (DemandProfile.Sets.cons .ignored [] (fun _ _ _ => False))
      ((proofErase Γ b).liftN 1) .sort .pi := by
    apply Obs.payload
    · exact ⟨A :: Γ, b.lift, .sort v, hΓA, rfl, hbL, sort_profile hΓA hbL,
        proofErase_liftN hΓ hΓA Ctx.LiftN.one hb⟩
    · exact TypeArgumentOrigin.refl hb
  have HF : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ b v)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ (.lam A b.lift))
      (.arrow .ignored .sort) (.app [] .pi) := by
    rw [EF]
    exact .lam ⟨Γ, _, _, hΓ, rfl, hf, HP, EF⟩ (by intro _ H; cases H) HB
  apply static_structure_dependent_payload_readout heq hs hΓ ht ?_ R
  rw [EE]
  exact .app ⟨Γ, _, _, hΓ, rfl, ht, sort_profile hΓ ht, EE⟩ HF (by intro _ H; cases H)

/-- Whole-root typing suffices for full constant-cut readout. Typed beta
supplies lower body typing directly, and Pi-assignment uniqueness recovers the
argument at the written annotation. No inverse weakening is used. -/
theorem static_structure_typed_constant_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app (.lam A b.lift) x) (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b.lift) x)) out) :
    ∃ b', env.IsDefEq univs Γ b b' (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ b) (proofErase Γ b') ∧ BetaRed out (proofErase Γ b') := by
  have RB : VExpr.BetaRed (.app (.lam A b.lift) x) b := by
    simpa only [VExpr.inst_lift] using (VExpr.BetaRed.beta (A := A) (b := b.lift) (a := x))
  have hb := (beta_eq hΓ ht RB).hasType.2
  obtain ⟨Q, B, hf, hxQ⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hf.lam_inv henv hΓ
  have hfA := HasType.lam hA (hb.weak henv.ordered)
  obtain ⟨⟨_, HQA⟩, _⟩ := (hf.uniqU henv hΓ hfA).forallE_inv henv hΓ
  exact static_structure_constant_cut_readout heq hs hΓ hb (HQA.defeq hxQ) R

/-- A type selector may first bind a type and then discard a value in an
arbitrary domain depending on that type. Every computation of the whole
application reads a forward history of the original type argument, even when
computation interleaves the two cuts and their dependent annotations. The
second argument may be a proof; neither argument needs native recovery. -/
theorem static_structure_dependent_type_selector_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.sort u))
    (hQ : env.HasType univs (.sort u :: Γ) Q (.sort w))
    (hy : env.HasType univs Γ y (Q.inst x))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.app (.lam (.sort u) (.lam Q (.bvar 1))) x) y)) out) :
    ∃ x', env.IsDefEq univs Γ x x' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ x') ∧ BetaRed out (proofErase Γ x') := by
  have hu := (hx.isType henv hΓ).choose_spec.sort_inv henv.ordered
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have hΓQ : OnCtx (Q :: .sort u :: Γ) (env.IsType univs) := ⟨hΓU, w, hQ⟩
  have hb : env.HasType univs (Q :: .sort u :: Γ) (.bvar 1) (.sort u) :=
    .bvar (.succ .zero)
  have hi := HasType.lam hQ hb
  have hf := HasType.lam hU hi
  have hfx : env.HasType univs Γ (.app (.lam (.sort u) (.lam Q (.bvar 1))) x)
      (.forallE (Q.inst x) (.sort u)) := hf.app hx
  have ht := hfx.app hy
  have Pi : Fits (.sort u :: Γ) (.forallE Q (.sort u)) (.arrow .ignored .sort) :=
    ⟨hi.isType henv hΓU, Q, .sort u, (hi.isType henv hΓU).choose_spec.toU,
      ⟨w, hQ⟩, sort_profile hΓQ hb⟩
  have Pf : Fits Γ (.forallE (.sort u) (.forallE Q (.sort u)))
      (.arrow .sort (.arrow .ignored .sort)) :=
    ⟨hf.isType henv hΓ, .sort u, .forallE Q (.sort u),
      (hf.isType henv hΓ).choose_spec.toU, sort_profile hΓ hx, Pi⟩
  have PiX : Fits Γ (.forallE (Q.inst x) (.sort u)) (.arrow .ignored .sort) :=
    ⟨hfx.isType henv hΓ, Q.inst x, .sort u, (hfx.isType henv hΓ).choose_spec.toU,
      hy.isType henv hΓ, sort_profile ⟨hΓ, hy.isType henv hΓ⟩
        (hx.weak henv.ordered)⟩
  have EB : proofErase (Q :: .sort u :: Γ) (.bvar 1) = .bvar 1 :=
    if_neg (not_isProof_of_sort hΓQ hb)
  have EI : proofErase (.sort u :: Γ) (.lam Q (.bvar 1)) =
      .lam (proofErase (.sort u :: Γ) Q) (.bvar 1) := by
    rw [show proofErase (.sort u :: Γ) (.lam Q (.bvar 1)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓU hi), EB]
  have EF : proofErase Γ (.lam (.sort u) (.lam Q (.bvar 1))) =
      .lam (proofErase Γ (.sort u)) (proofErase (.sort u :: Γ) (.lam Q (.bvar 1))) :=
    if_neg (Pf.not_isProof hΓ (.arrow (.arrow .sort)) hf)
  have EX : proofErase Γ (.app (.lam (.sort u) (.lam Q (.bvar 1))) x) =
      .app (proofErase Γ (.lam (.sort u) (.lam Q (.bvar 1)))) (proofErase Γ x) :=
    if_neg (PiX.not_isProof hΓ (.arrow .sort) hfx)
  have EY : proofErase Γ (.app (.app (.lam (.sort u) (.lam Q (.bvar 1))) x) y) =
      .app (proofErase Γ (.app (.lam (.sort u) (.lam Q (.bvar 1))) x)) (proofErase Γ y) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HF : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ x u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.lam (.sort u) (.lam Q (.bvar 1))))
      (.arrow .sort (.arrow .ignored .sort)) (.app [.pi] (.app [] .pi)) := by
    rw [EF]
    apply Obs.lam ⟨Γ, _, _, hΓ, rfl, hf, Pf, EF⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .sort
    · rw [EI]
      apply Obs.lam ⟨.sort u :: Γ, _, _, hΓU, rfl, hi, Pi, EI⟩
      · intro _ H; cases H
      · exact .var ⟨Q :: .sort u :: Γ, _, _, hΓQ, rfl, hb, sort_profile hΓQ hb, EB⟩
          .sort ⟨rfl, by simp⟩
  have HX : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ x u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ x) .sort .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using
          (show Typing (proofEraseCtx Γ) (proofErase Γ x) .sort from
            ⟨Γ, x, .sort u, hΓ, rfl, hx, sort_profile hΓ hx, rfl⟩))
        (TypeArgumentOrigin.refl (Step := ErasedStaticStructureEtaExpansionUnion D) hx))
  apply static_structure_dependent_payload_readout heq hs hΓ ht ?_ R
  rw [EY]
  apply Obs.app ⟨Γ, _, _, hΓ, rfl, ht, sort_profile hΓ ht, EY⟩ (keys := [])
  · rw [EX]
    apply Obs.app ⟨Γ, _, _, hΓ, rfl, hfx, PiX, EX⟩ HF
    intro key hk; obtain rfl := List.mem_singleton.1 hk; exact HX
  · intro _ H; cases H

end Lean4Lean.VEnv.Strengthening
