import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery

/-! # Reducing common-native instantiation to one computed binder

A common argument type can be realized as an actual computed binder. Existing
exact native substitution then applies at that binder. The remaining issue is
forward transport of the body's native certificate from its old binder, with a
computational residual on the selected type. This module makes that obligation
explicit and proves the reduction; it does not assert the obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- A retained argument recovers a reduct of its assigned type. Any common
reduct of an assigned and native type supplies this condition by conversion of
the native certificate. Proof arguments need no native evidence. -/
def CommonNativeArgument (D : PureObservation.Definitions) (Γ : List VExpr) (x A : VExpr) : Prop :=
  ¬ IsProof Γ x → ∃ native,
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) native ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) native

/-- The open forward-binder obligation: after A computes to C, native recovery
under A transports under C with a forward residual on its selected type.
The expression is fixed. This definition supplies no transport proof. -/
def NativeForwardBinder (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A C u e T out}, OnCtx Γ (env.IsType univs) →
    env.IsDefEq univs Γ A C (.sort u) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C) →
    env.HasType univs (A :: Γ) e T →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out →
    ∃ native, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
        (proofErase (C :: Γ) e) native ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ)) out native

/-- The open single-instantiation obligation with common native arguments.
The result need only recover a reduct of the old selected output after
substitution. This definition supplies no image-coverage or transport proof. -/
def NativeCommonInstantiation (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A x b B out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ x A →
    CommonNativeArgument D Γ x A → env.HasType univs (A :: Γ) b B →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out →
    ∃ native, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) native ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) native

/-- An explicit common type gives the retained-argument condition without
requiring native recovery of the assigned type itself. -/
theorem CommonNativeArgument.of_join
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) native)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) native shared) :
    CommonNativeArgument D Γ x A := fun _ => ⟨shared, RN.convert RB, RA⟩

/-- Exact native arguments instantiate arbitrary finite-union computation.
This is the already established exact-image transport, with its stage bounds
collected from the argument and computation certificates. -/
theorem static_structure_union_compute_inst_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (hb : env.HasType univs (A :: Γ) b B)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨n, RC⟩ := RC.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  obtain ⟨k, RX⟩ := RX.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have R := StaticStructureEtaNativeSubstitution.compute heq hs RC hΓA hb rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ W ES (NativeImageTransport.Images.inst RX))
  rw [← proofErase_subst_with hΓ W hb ES] at R
  have R' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+k)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using R
  exact R'.mono (fun H => ⟨n+k, H⟩)

/-- Forward native transport across a single computed binder is sufficient
for general single instantiation at a common native argument. The shared type
is realized from the assigned-type path, then both recovery and its residual
use exact substitution at that computed binder. No confluence is assumed. -/
theorem NativeForwardBinder.common_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : NativeForwardBinder D) : NativeCommonInstantiation D := by
  intro Γ A x b B out hΓ hx HI hb RN
  classical
  by_cases hp : IsProof Γ x
  · exact ⟨_, static_structure_union_recovery_inst heq hs hΓ hx
      (fun hn => (hn hp).elim) hb RN, .refl⟩
  obtain ⟨shared, RX, RA⟩ := HI hp
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  obtain ⟨C, HAC, EC⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl RA
  rw [← EC] at RX RA
  have hxC := HAC.defeq hx
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.2⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hbC := hb.defeqDFC henv HC
  obtain ⟨native, RB, RT⟩ := HF hΓ HAC RA hb RN
  have RBI := static_structure_union_recovery_inst heq hs hΓ hxC (fun _ => RX) hbC RB
  obtain ⟨O, hbO, EO⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb RN
  obtain ⟨_, hO⟩ := hbO.isType henv hΓA
  have hOC := hO.defeqDFC henv HC
  have EOC : proofErase (C :: Γ) O = out :=
    (proofErase_defeqCtx hΓA HC hO).symm.trans EO
  have RT' := static_structure_union_compute_inst_native heq hs hΓ hxC RX hOC (EOC ▸ RT)
  rw [proofErase_instN hΓC hxC Ctx.InstN.zero hOC, EOC] at RT'
  exact ⟨_, RBI, RT'⟩

/-- Conversely, general common-native single instantiation transports a
computed binder forward. Insert the target binder below the old one, then
instantiate the old binder with the new variable. The argument certificate is
just lookup followed by the weakened domain computation. -/
theorem NativeCommonInstantiation.forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HI : NativeCommonInstantiation D) : NativeForwardBinder D := by
  intro Γ A C u b B out hΓ HAC RA hb RN
  have hA := HAC.hasType.1
  have hC := HAC.hasType.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hΓAC : OnCtx (A.lift :: C :: Γ) (env.IsType univs) :=
    ⟨hΓC, u, hA.weakN henv Ctx.LiftN.one⟩
  have W : Ctx.LiftN 1 1 (A :: Γ) (A.lift :: C :: Γ) := Ctx.LiftN.one.succ
  have hbx := hb.weakN henv W
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hx : env.HasType univs (C :: Γ) (.bvar 0) A.lift :=
    (HAC.weakN henv Ctx.LiftN.one).symm.defeq (show env.HasType univs (C :: Γ) (.bvar 0) C.lift from .bvar .zero)
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RNU := RN.rename hrename (ContextRenaming.of_liftN hΓA hΓAC W)
  simp only [subst_bvar_liftN] at RNU
  rw [← proofErase_liftN hΓA hΓAC W hb] at RNU
  have RAL := RA.rename hrename (ContextRenaming.of_liftN hΓ hΓC Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at RAL
  have Harg : CommonNativeArgument D (C :: Γ) (.bvar 0) A.lift := by
    intro hn
    refine ⟨proofErase (C :: Γ) C.lift, proofErase_scoped_lookup_recovery hΓC .zero hn .refl, ?_⟩
    simpa only [proofErase_liftN hΓ hΓC Ctx.LiftN.one hA,
      proofErase_liftN hΓ hΓC Ctx.LiftN.one hC] using RAL
  obtain ⟨native, RB, RT⟩ := HI hΓC hx Harg hbx RNU
  simp only [VExpr.inst_liftN_bvar] at RB
  obtain ⟨O, hbO, EO⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb RN
  obtain ⟨_, hO⟩ := hbO.isType henv hΓA
  have EOU := proofErase_liftN hΓA hΓAC W hO
  have EOI := proofErase_instN hΓAC hx Ctx.InstN.zero (hO.weakN henv W)
  rw [VExpr.inst_liftN_bvar, EOU, EO] at EOI
  have EOC : proofErase (C :: Γ) O = out :=
    (proofErase_defeqCtx hΓA HC hO).symm.trans EO
  rw [← EOI, EOC] at RT
  exact ⟨native, RB, RT⟩

/-- Common-native single instantiation is exactly the forward transport
problem for one computed binder in the full structure/function-eta language.
Neither side is asserted here; this is a proved reduction in both directions,
not a claim of a new sufficient obligation smaller than PropFront. -/
theorem native_common_instantiation_iff_forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    NativeCommonInstantiation D ↔ NativeForwardBinder D :=
  ⟨fun H => H.forward_binder heq hs, fun H => H.common_instantiation heq hs⟩

end Lean4Lean.VEnv.Strengthening
