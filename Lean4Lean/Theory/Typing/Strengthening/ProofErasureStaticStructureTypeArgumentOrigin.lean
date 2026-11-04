import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeArgumentTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureDependentReturn

/-! # Neutral type applications retain arbitrary argument histories

The argument may have any typed syntax. Its whole computation history descends
through temporary control binders, so a reduced application beta-reads as the
same neutral head applied to a computed representative of the original argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.TypeArgumentObservation
variable [Params] {D : PureObservation.Definitions}

/-- A marked argument retains its actual typed representative and complete
lower computation from the original argument. -/
def TypeArgumentOrigin (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (A : VExpr) (u : VLevel) (out : ProofShape) : Prop :=
  ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧ proofErase Γ A' = out ∧
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) out

/-- An original type starts with its reflexive history. -/
theorem TypeArgumentOrigin.refl (hA : env.HasType univs Γ A (.sort u)) :
    TypeArgumentOrigin Step Γ A u (proofErase Γ A) := ⟨A, hA, rfl, .refl⟩

/-- Certificate descent updates an arbitrary argument history below every
temporary control prefix. No native recovery or confluence premise is used. -/
theorem typeArgumentOrigin_closure
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    TypeArgumentClosure Step Γ (TypeArgumentOrigin Step Γ A u) := by
  intro Γ' n a out hΓ' W HP R
  obtain ⟨A', HA, rfl, RA⟩ := HP
  obtain ⟨A'', HA', RC, E⟩ := proofErase_scoped_compute_certificate_descend
    hstep hΓ hΓ' W HA.hasType.2 rfl R
  exact ⟨proofErase Γ A'', ⟨A'', HA.trans HA', rfl, RA.trans RC⟩, E⟩

/-- Every full-union computation of F A beta-reads as F A', where A'
retains a typed computation from the arbitrary original type A. This removes
the variable and literal-Pi restrictions on arguments. F remains a neutral
universe-to-universe variable; data arguments are not covered by this theorem. -/
theorem static_structure_neutral_type_argument_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ A)) out) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧
      ProofShape.BetaRed out (.app (.bvar f) (proofErase Γ A')) := by
  have ht : env.HasType univs Γ (.app (.bvar f) A) (.sort v) := hf.app hA
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (not_isProof_function_to_sort hΓ hf)
  have EE : proofErase Γ (.app (.bvar f) A) = .app (.bvar f) (proofErase Γ A) := by
    rw [show proofErase Γ (.app (.bvar f) A) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), EF]
  have HF : ControlTyping (proofEraseCtx Γ) (.bvar f) (.arrow (.sort u) (.sort v)) :=
    ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have HA : ControlTyping (proofEraseCtx Γ) (proofErase Γ A) (.sort u) := ⟨Γ, _, hΓ, rfl, hA, rfl⟩
  have HT : ControlTyping (proofEraseCtx Γ) (.app (.bvar f) (proofErase Γ A)) (.sort v) :=
    ⟨Γ, _, hΓ, rfl, ht, EE⟩
  let S : ControlObservation.Sets := fun j t o =>
    j = f ∧ t = .arrow (.sort u) (.sort v) ∧ o = .app [.pi] .sort
  have HS : S.Typed (proofEraseCtx Γ) := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HF
  have H : Obs (TypeArgumentOrigin (ErasedStaticStructureEtaExpansionUnion D) Γ A u)
      0 (proofEraseCtx Γ) S (.app (.bvar f) (proofErase Γ A)) (.sort v) .sort := by
    apply Obs.app HT (keys := [.pi])
    · exact .var HF (.fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .payload)
        .neutral) ⟨rfl, rfl, rfl⟩
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      simpa only [ProofShape.liftN_zero] using
        (Obs.payload (n := 0) (S := S) (by simpa only [ProofShape.liftN_zero] using HA)
          (TypeArgumentOrigin.refl hA))
  have HO := proofErase_scoped_compute_typeArgumentObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_argument_control heq hs)
    (typeArgumentOrigin_closure (erased_static_structure_eta_expansion_union_certificate_descent heq hs) hΓ)
    R hΓ (Ctx.LiftN.zero []) ht rfl EE HS H
  have HR := HO.realizes (head := .bvar f)
    (show PiOriginObservation.FixedTail 0 0 ProofShape.Subst.id from fun _ => rfl)
    (fun j t key hj => by
      obtain ⟨rfl, rfl, rfl⟩ := hj
      simp only [Realizes, ProofShape.Subst.id, ProofShape.liftN_zero]
      intro a ha
      have HA := ha .pi (by simp)
      simp only [Realizes, ProofShape.liftN_zero] at HA
      obtain ⟨a', HP, RB⟩ := HA
      exact ⟨a', HP, .app .refl RB⟩)
  simp only [ProofShape.subst_id, Realizes, ProofShape.liftN_zero] at HR
  obtain ⟨a', ⟨A', HA', rfl, RA⟩, RB⟩ := HR
  exact ⟨A', HA', RA, RB⟩

/-- Local joining at an arbitrary type argument lifts through its neutral
universe-to-universe family. The supplied argument-joining premise is explicit;
this does not assert global type confluence. -/
theorem static_structure_neutral_type_argument_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (HJ : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ A)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ A)) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨_, _, RAL, BL⟩ := static_structure_neutral_type_argument_origin heq hs hΓ hA hf RL
  obtain ⟨_, _, RAR, BR⟩ := static_structure_neutral_type_argument_origin heq hs hΓ hA hf RR
  obtain ⟨shared, JL, JR⟩ := HJ RAL RAR
  exact ⟨.app (.bvar f) shared,
    (ScopedCompute.beta BL).trans (.app .refl JL),
    (ScopedCompute.beta BR).trans (.app .refl JR)⟩

/-- For variable/universe/Pi arguments, the known return theorem discharges
the argument obligation and returns the whole application exactly. -/
theorem static_structure_neutral_dependent_argument_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (HA : UniversePiSyntax A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ A)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.bvar f) (proofErase Γ A)) := by
  obtain ⟨_, _, RA, RB⟩ := static_structure_neutral_type_argument_origin heq hs hΓ hA hf R
  exact (ScopedCompute.beta RB).trans
    (.app .refl (static_structure_dependent_return heq hs hΓ hA HA RA))

end Lean4Lean.VEnv.Strengthening
