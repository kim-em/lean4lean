import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureTypeArgumentOrigin

/-! # Complete continuations of constant and identity cuts on types

A type payload survives arbitrary full-union computation in a typed control
program. Constant and identity cuts therefore admit pure-beta readout after
unrestricted continuations, including computation after the original cut has
contracted. Their supplied arguments need ordinary sort typing only.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.TypeArgumentObservation
variable [Params] {D : PureObservation.Definitions}

/-- A type payload observed in a sort-valued control program survives its
entire computation. This is a forward history of the original payload with a
pure-beta residual from the final output. No joining hypothesis is required.
The observation certificate is explicit; arbitrary type-valued beta redexes
are not asserted to have one. -/
theorem static_structure_type_payload_program_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v))
    (H : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ e) (.sort v) .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧ BetaRed out (proofErase Γ A') := by
  have HO := proofErase_scoped_compute_typeArgumentObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_argument_control heq hs)
    (typeArgumentOrigin_closure (erased_static_structure_eta_expansion_union_certificate_descent heq hs) hΓ)
    R hΓ (Ctx.LiftN.zero []) ht rfl rfl (by intro _ _ _ H; exact H.elim) H
  have HR := HO.realizes (head := .proof)
    (show PiOriginObservation.FixedTail 0 0 ProofShape.Subst.id from fun _ => rfl)
    (fun _ _ _ H => H.elim)
  simp only [ProofShape.subst_id, Realizes, ProofShape.liftN_zero] at HR
  obtain ⟨_, ⟨A', HA', rfl, RA⟩, RB⟩ := HR
  exact ⟨A', HA', RA, RB⟩

/-- A constant cut supplied with any ordinary type admits complete readout
of the discarded-binder payload. The written annotation may be any type
ordinarily equal to the argument's universe. The whole continuation is arbitrary;
neither the argument nor its later images need native recovery. -/
theorem static_structure_constant_type_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x (.sort w))
    (HL : env.IsDefEq univs Γ L (.sort w) (.sort z))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam L A.lift) x)) out) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧ BetaRed out (proofErase Γ A') := by
  have hL := HL.hasType.1
  have hΓL : OnCtx (L :: Γ) (env.IsType univs) := ⟨hΓ, z, hL⟩
  have hb : env.HasType univs (L :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  have hf := HasType.lam hL hb
  have hxL := HL.symm.defeq hx
  have ht : env.HasType univs Γ (.app (.lam L A.lift) x) (.sort u) := hf.app hxL
  have hu := (hA.isType henv hΓ).choose_spec.sort_inv henv.ordered
  have hfS : env.HasType univs Γ (.lam L A.lift) (.forallE (.sort w) (.sort u)) :=
    (IsDefEq.forallEDF HL (HasType.sort hu)).defeq hf
  have EF : proofErase Γ (.lam L A.lift) =
      .lam (proofErase Γ L) ((proofErase Γ A).liftN 1) := by
    rw [show proofErase Γ (.lam L A.lift) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf), proofErase_liftN hΓ hΓL Ctx.LiftN.one hA]
  have EE : proofErase Γ (.app (.lam L A.lift) x) =
      .app (proofErase Γ (.lam L A.lift)) (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HB : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      1 (proofEraseCtx (L :: Γ)) (ControlObservation.Sets.cons (.sort w) [] (fun _ _ _ => False))
      ((proofErase Γ A).liftN 1) (.sort u) .pi := by
    apply Obs.payload
    · exact ⟨L :: Γ, A.lift, hΓL, rfl, hb, proofErase_liftN hΓ hΓL Ctx.LiftN.one hA⟩
    · exact TypeArgumentOrigin.refl hA
  have HF : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ (.lam L A.lift))
      (.arrow (.sort w) (.sort u)) (.app [] .pi) := by
    rw [EF]
    exact .lam ⟨Γ, _, hΓ, rfl, hfS, EF⟩ (by intro _ H; cases H) HB
  apply static_structure_type_payload_program_readout heq hs hΓ ht ?_ R
  rw [EE]
  exact .app ⟨Γ, _, hΓ, rfl, ht, EE⟩ HF (by intro _ H; cases H)

/-- Identity cuts at arbitrary written annotations convertible to a universe
retain the actual type argument as their payload through every continuation.
This does not require a native identity-expansion guard, or a computational path
from the written annotation to the displayed universe. -/
theorem static_structure_identity_type_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.sort u))
    (HL : env.IsDefEq univs Γ L (.sort u) (.sort z))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam L (.bvar 0)) x)) out) :
    ∃ x', env.IsDefEq univs Γ x x' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ x') ∧ BetaRed out (proofErase Γ x') := by
  have hL := HL.hasType.1
  have hΓL : OnCtx (L :: Γ) (env.IsType univs) := ⟨hΓ, z, hL⟩
  have hb : env.HasType univs (L :: Γ) (.bvar 0) (.sort u) :=
    (HL.weak henv.ordered).defeq (HasType.bvar .zero)
  have hf := HasType.lam hL hb
  have hxL := HL.symm.defeq hx
  have ht : env.HasType univs Γ (.app (.lam L (.bvar 0)) x) (.sort u) := hf.app hxL
  have hu := (hx.isType henv hΓ).choose_spec.sort_inv henv.ordered
  have hfS : env.HasType univs Γ (.lam L (.bvar 0)) (.forallE (.sort u) (.sort u)) :=
    (IsDefEq.forallEDF HL (HasType.sort hu)).defeq hf
  have EB : proofErase (L :: Γ) (.bvar 0) = .bvar 0 := if_neg (not_isProof_of_sort hΓL hb)
  have EF : proofErase Γ (.lam L (.bvar 0)) = .lam (proofErase Γ L) (.bvar 0) := by
    rw [show proofErase Γ (.lam L (.bvar 0)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf), EB]
  have EE : proofErase Γ (.app (.lam L (.bvar 0)) x) =
      .app (proofErase Γ (.lam L (.bvar 0))) (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HF : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ x u)
      0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ (.lam L (.bvar 0)))
      (.arrow (.sort u) (.sort u)) (.app [.pi] .pi) := by
    rw [EF]
    apply Obs.lam ⟨Γ, _, hΓ, rfl, hfS, EF⟩
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact .payload
    · exact .var ⟨L :: Γ, _, hΓL, rfl, hb, EB⟩ .payload ⟨rfl, by simp⟩
  apply static_structure_type_payload_program_readout heq hs hΓ ht ?_ R
  rw [EE]
  apply Obs.app ⟨Γ, _, hΓ, rfl, ht, EE⟩ HF
  intro key hk
  obtain rfl := List.mem_singleton.1 hk
  simpa only [ProofShape.liftN_zero] using
    (Obs.payload (n := 0) (S := fun _ _ _ => False)
      (by simpa only [ProofShape.liftN_zero] using ControlTyping.of_typed hΓ hx)
      (TypeArgumentOrigin.refl (Step := ErasedStaticStructureEtaExpansionUnion D) hx))

/-- Every ordinarily typed identity beta cut whose result is a type has the
complete continuation readout above. Sort typing of the argument and conversion
of the written annotation are derived from the whole cut's typing. This covers
the full identity-cut case of type-valued beta stripping without HJ or HF. -/
theorem static_structure_typed_identity_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app (.lam L (.bvar 0)) x) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam L (.bvar 0)) x)) out) :
    ∃ x', env.IsDefEq univs Γ x x' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ x') ∧ BetaRed out (proofErase Γ x') := by
  obtain ⟨Q, B, hf, hxQ⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨z, hL⟩, _, _⟩ := hf.lam_inv henv hΓ
  have hfL : env.HasType univs Γ (.lam L (.bvar 0)) (.forallE L L.lift) :=
    .lam hL (.bvar .zero)
  obtain ⟨⟨_, HQL⟩, _⟩ := (hf.uniqU henv hΓ hfL).forallE_inv henv hΓ
  have hx := HQL.defeq hxQ
  have Hβ : env.IsDefEq univs Γ (.app (.lam L (.bvar 0)) x) x L := by
    simpa only [VExpr.inst_lift, VExpr.inst, instVar, Nat.lt_irrefl,
      ↓reduceIte, Nat.sub_self, VExpr.liftN_zero] using
      (IsDefEq.beta (HasType.bvar (Γ := L :: Γ) .zero) hx)
  have hxSort := (IsDefEq.trans_l henv hΓ ht Hβ).hasType.2
  have HL := (hx.uniqU henv hΓ hxSort).of_l henv hΓ hL
  exact static_structure_identity_type_cut_readout heq hs hΓ hxSort HL R

end Lean4Lean.VEnv.Strengthening
