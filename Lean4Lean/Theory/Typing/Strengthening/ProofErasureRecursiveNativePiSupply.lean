import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation

/-! # Arbitrary native application histories of reified families

Native recovery supplies an exact sequence of selected Pi conversions and
argument instantiations. Recursive observations follow that sequence through
opaque residuals, retaining the final selected output without normalization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

namespace ProofShape
/-- The selected types of an application spine, with every conversion tail
retained. Only the next Pi must be literal when an argument is supplied. -/
inductive SelectedPiSupply (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : ProofShape → List ProofShape → ProofShape → Prop where
  | done : ScopedCompute Step Δ T out → SelectedPiSupply Step Δ T [] out
  | app : ScopedCompute Step Δ T (.forallE A B) →
      SelectedPiSupply Step Δ (B.inst image) images out →
      SelectedPiSupply Step Δ T (image :: images) out

/-- An earlier type computation appends to the first selected conversion. -/
theorem SelectedPiSupply.precompute
    (W : SelectedPiSupply Step Δ T images out) (R : ScopedCompute Step Δ S T) :
    SelectedPiSupply Step Δ S images out := by
  cases W with
  | done RC => exact .done (R.trans RC)
  | app RC W => exact .app (R.trans RC) W

variable [Params]

/-- Every native recovery of an application spine has such a selected-type
history starting at an actual native output of its original head. -/
theorem ScopedTypeRecovery.selected_supply
    (RN : ScopedTypeRecovery Step Δ (ProofShape.mkApps f images) out) :
    ∃ T, ScopedTypeRecovery Step Δ f T ∧ SelectedPiSupply Step Δ T images out := by
  induction images generalizing f with
  | nil => exact ⟨out, RN, .done .refl⟩
  | cons image images ih =>
    obtain ⟨T, RF, W⟩ := ih RN
    obtain ⟨A, B, RF0, RT⟩ := RF.app_origin
    exact ⟨.forallE A B, RF0, .app .refl (W.precompute RT)⟩
end ProofShape

variable [Params] {D : PureObservation.Definitions}

private theorem spine_head_type
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T) :
    ∃ A, env.HasType univs Γ f A := by
  induction args generalizing f with
  | nil => exact ⟨T, ht⟩
  | cons x args ih =>
    obtain ⟨B, HB⟩ := ih ht
    obtain ⟨A, C, HF, _⟩ := HB.app_inv henv hΓ
    exact ⟨.forallE A C, HF⟩

private theorem spine_function_eq
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEqU univs Γ f g)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T) :
    env.IsDefEqU univs Γ (VExpr.mkApps f args) (VExpr.mkApps g args) := by
  induction args generalizing f g with
  | nil => exact HE
  | cons x args ih =>
    obtain ⟨B, HB⟩ := spine_head_type (f := .app f x) hΓ ht
    obtain ⟨A, C, HF, HX⟩ := HB.app_inv henv hΓ
    exact ih ((IsDefEq.appDF (HE.of_l henv hΓ HF) HX).toU) ht

/-- Recursive observations follow arbitrary selected-type supply histories.
All supplied arguments may compute independently; their images are realized
at each selected domain using ordinary typing, without native certificates. -/
theorem NativeFamilyPiObservation.supply_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiObservation D Γ g u args.length [] T)
    (ht : env.HasType univs Γ (VExpr.mkApps g args) (.sort v))
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (W : SelectedPiSupply (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T images out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps g args)) out := by
  induction args generalizing g T images with
  | nil =>
    cases RX
    cases W with
    | done R => exact (NativeFamilyPiObservation.compute (pending := []) heq hs hΓ hΓ H R).finish
  | cons x args ih =>
    change env.HasType univs Γ (VExpr.mkApps (.app g x) args) (.sort v) at ht
    cases RX with
    | cons RImage RImages =>
      cases W with
      | @app _ rawA rawB image images _ RPi W =>
        have HP := (NativeFamilyPiObservation.compute (pending := []) heq hs hΓ hΓ H RPi).selected_pi
        obtain ⟨A, B, hA, hB, EA, EB, HBody⟩ := HP
        obtain ⟨ds, C, hlen, HF⟩ := HBody.witness
        have hf : env.HasType univs Γ g (.forallE A (VExpr.wrapForalls ds (.sort u))) := HF.typed
        obtain ⟨V, hApp⟩ := spine_head_type (f := .app g x) hΓ ht
        obtain ⟨A₀, B₀, hf₀, hx₀⟩ := hApp.app_inv henv hΓ
        obtain ⟨⟨q, HA⟩, _⟩ := (hf₀.uniqU henv hΓ hf).forallE_inv henv hΓ
        have hx := HA.defeq hx₀
        obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize
          (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RImage
        have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
        have HS := NativeFamilyPiObservation.supply (pending := []) hΓ hΓA HXY.hasType.2 HBody
        have HE := IsDefEq.appDF hf HXY
        have HEApps := spine_function_eq hΓ HE.toU ht
        have ht' := (HEApps.of_l henv hΓ ht).hasType.2
        have RT := ih HS ht' RImages (by rwa [← EY] at W)
        have HX := HF.apply hΓ hx
        have HY := HF.apply hΓ HXY.hasType.2
        have RH : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ (.app g x)) (proofErase Γ (.app g y)) := by
          rw [show proofErase Γ (.app g x) = .app _ _ from
            if_neg (not_isProof_telescope_to_sort hΓ HX.typed),
            show proofErase Γ (.app g y) = .app _ _ from
            if_neg (not_isProof_telescope_to_sort hΓ HY.typed), EY]
          exact .app .refl RImage
        have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ (VExpr.mkApps (.app g x) args))
            (proofErase Γ (VExpr.mkApps (.app g y) args)) := by
          rw [proofErase_mkApps hΓ ht (not_isProof_of_sort hΓ ht),
            proofErase_mkApps hΓ ht' (not_isProof_of_sort hΓ ht')]
          exact RH.mkApps (List.Forall₂.rfl (fun _ _ => .refl))
        exact RP.trans RT

/-- Arbitrary finite native application histories preserve the original
reified family application's ancestry. Conversions may occur at every prefix,
with opaque residual types between applications. The original head's fixed
type-origin property and the family's exact native telescope remain explicit;
no native argument, literal-checkpoint, beta-strip, or type-fork premise occurs. -/
theorem NativeFamilyPiHistory.native_spine_application_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ g u ds B)
    (hlen : ds.length = args.length)
    (ht : env.HasType univs Γ (VExpr.mkApps g args) (.sort v))
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ds B)) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps f images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps g args)) out := by
  obtain ⟨T, RF, W⟩ := RN.selected_supply
  have HO := NativeFamilyPiObservation.of_history (pending := []) hΓ H
  rw [hlen] at HO
  exact HO.supply_history heq hs hΓ ht RX (W.precompute (HN RF))

/-- Literal paired declarations discharge the initial native-header and
term-origin premises for a fieldless constructor telescope of arbitrary arity.
Every selected native type of its computed-argument application is reached
from the original family application, with all intermediate conversions kept.
Nonliteral declaration headers and constructor field suffixes are not covered. -/
theorem static_structure_declared_constructor_spine_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants ctor = some ci) (hwc : ∀ l ∈ cls, l.WF univs)
    (hlc : cls.length = ci.uvars)
    (hf : env.constants family = some fi) (hwf : ∀ l ∈ fls, l.WF univs)
    (hlf : fls.length = fi.uvars)
    (HTf : fi.type.instL fls = VExpr.wrapForalls ds (.sort u))
    (HTc : ci.type.instL cls =
      VExpr.wrapForalls ds (etaOpen ds.length (.const family fls)))
    (HA : TelInst env univs Γ ds args)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor cls) images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const family fls) args)) out := by
  have hft : env.HasType univs Γ (.const family fls) (VExpr.wrapForalls ds (.sort u)) :=
    HTf ▸ HasType.const hf hwf hlf
  have EF : proofErase Γ (.const family fls) = .const family fls :=
    if_neg (not_isProof_telescope_to_sort hΓ hft)
  have hfc : env.HasType univs [] (.const family fls) (fi.type.instL fls) := .const hf hwf hlf
  obtain ⟨_, hfT⟩ := hfc.isType henv (by trivial)
  have Eft := proofErase_closed_context ((henv.ordered.closedC hf).instL) hfT hΓ
  have RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.const family fls)) (proofErase Γ (VExpr.wrapForalls ds (.sort u))) := by
    rw [EF, ← HTf, Eft]
    exact .const hf hwf hlf
  have H := NativeFamilyPiHistory.initial heq hs hΓ hft RF
  have hct : env.HasType univs [] (.const ctor cls) (ci.type.instL cls) := .const hc hwc hlc
  obtain ⟨_, hcT⟩ := hct.isType henv (by trivial)
  have Ect := proofErase_closed_context ((henv.ordered.closedC hc).instL) hcT hΓ
  have ht : env.HasType univs Γ (VExpr.mkApps (.const family fls) args) (.sort u) := by
    simpa only [VExpr.instOuter_sort] using HasType.mkApps_of_tel hft HA
  apply H.native_spine_application_origin heq hs hΓ HA.1.symm ht ?_ RX RN
  intro T RT
  have RC := RT.const_compute hc
  rwa [← Ect, HTc] at RC

end Lean4Lean.VEnv.Strengthening
