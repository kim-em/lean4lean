import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredFieldSupply

/-! # Native histories from observed, nonliteral declaration headers

A literal telescope may compute to the stored header before native supply
starts. Its recursive observation then follows that stored header and every
selected application. This is directed header ancestry, not arbitrary ordinary
header conversion. Controlled constant wrappers give a concrete nonliteral case.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An observed original header suffices for exact ignored-field ancestry.
The header need not be a literal Pi, and selected native histories may convert
at every application prefix. Its native outputs must still retain this header
as a computation ancestor; ordinary typing alone does not supply that fact. -/
theorem IgnoredFieldPiObservation.native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : IgnoredFieldPiObservation D Γ result u args.length [] (proofErase Γ T))
    (hf : env.HasType univs Γ f T)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) S)
    (HN : ∀ {U}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) head U →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ T) U)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps head images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ result) out := by
  obtain ⟨U, RF, W⟩ := RN.selected_supply
  exact H.supply_history heq hs hΓ hf ht RX (W.precompute (HN RF))

/-- A computation from a literal ignored-field telescope to the stored
constant header initializes exact selected-output ancestry. The stored header
may be opaque or contain beta controls. The direction of the header path is
essential: a computation only from the stored header to a telescope does not
supply this invariant, and ordinary header equality is not substituted for it. -/
theorem static_structure_declared_computed_field_header_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hg : env.HasType univs Γ result (.sort u))
    (hc : env.constants ctor = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HA : TelInst env univs Γ fields args)
    (hctx : OnCtx (fields.reverse ++ Γ) (env.IsType univs))
    (RH : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls fields (result.liftN fields.length)))
      (proofErase Γ (ci.type.instL ls)))
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor ls) images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ result) out := by
  have HW : Ctx.LiftN fields.length 0 Γ (fields.reverse ++ Γ) :=
    .zero fields.reverse (by simp)
  obtain ⟨w, hPi⟩ := VExpr.wrapForalls_defeq hctx (hg.weakN henv HW)
  have hf : env.HasType univs Γ (.const ctor ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨T', HT', ET'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hPi.hasType.1 rfl rfl RH
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HT'.hasType.2 (hf.isType henv hΓ).choose_spec ET').2
    (not_isProof_of_sort hΓ HT'.hasType.2)
  have HE := HT'.toU.trans henv hΓ (HN.defeq hΓ)
  have hfPi := hf.defeqU_r henv hΓ HE.symm
  have ht := HasType.mkApps_of_tel hfPi HA
  have HO := IgnoredFieldPiObservation.of_telescope (D := D) (pending := []) hΓ hg hctx
  have HO' : IgnoredFieldPiObservation D Γ result u args.length []
      (proofErase Γ (VExpr.wrapForalls fields (result.liftN fields.length))) := by
    simpa only [← HA.1, List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using HO
  have HH := IgnoredFieldPiObservation.compute (pending := []) heq hs hΓ hΓ HO' RH
  have hfc : env.HasType univs [] (.const ctor ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hcT⟩ := hfc.isType henv (by trivial)
  have Ect := proofErase_closed_context ((henv.ordered.closedC hc).instL) hcT hΓ
  apply HH.native_origin heq hs hΓ hf ht ?_ RX RN
  intro U RU
  exact Ect ▸ RU.const_compute hc

/-- A stored header may wrap the entire field telescope in a constant beta
redex. The original result still reaches every selected native output exactly,
including all conversions before and between field applications. The header
ancestry premise is discharged by the actual controlled expansion rule. -/
theorem static_structure_declared_constant_wrapped_field_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hg : env.HasType univs Γ result (.sort u))
    (hc : env.constants ctor = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HT : ci.type.instL ls = .app (.lam (.sort (.succ .zero))
      (VExpr.wrapForalls fields (result.liftN fields.length)).lift) (.sort .zero))
    (HA : TelInst env univs Γ fields args)
    (hctx : OnCtx (fields.reverse ++ Γ) (env.IsType univs))
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor ls) images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ result) out := by
  have HW : Ctx.LiftN fields.length 0 Γ (fields.reverse ++ Γ) :=
    .zero fields.reverse (by simp)
  obtain ⟨w, hPi⟩ := VExpr.wrapForalls_defeq hctx (hg.weakN henv HW)
  apply static_structure_declared_computed_field_header_origin heq hs hΓ hg hc hw hl HA hctx ?_ RX RN
  rw [HT, proofErase_constantExpansion hΓ hPi.hasType.1 (not_isProof_of_sort hΓ hPi.hasType.1)]
  exact .base ⟨0, .inr (.intro (mt proofErase_eq_proof.1 (not_isProof_of_sort hΓ hPi.hasType.1)))⟩

end Lean4Lean.VEnv.Strengthening
