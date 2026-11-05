import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredFieldObservation

/-! # Exact selected native outputs through field-independent results

Ordinary typing of the term application validates each selected field domain.
The ignored-field observation retains the lower result path through every
conversion and substitution, including opaque residual telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private spine_head_type spine_function_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply
variable [Params] {D : PureObservation.Definitions}

/-- A selected-type supply history preserves a lower result that ignores all
its fields. Only ordinary typing of the term and its application is needed to
validate selected domains. Arguments may compute independently and never need
native recovery, including proof arguments and dependent later fields. -/
theorem IgnoredFieldPiObservation.supply_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : IgnoredFieldPiObservation D Γ g u args.length [] (proofErase Γ T))
    (hf : env.HasType univs Γ f T)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) S)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (W : SelectedPiSupply (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) images out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ g) out := by
  induction args generalizing f T images with
  | nil =>
    cases RX
    cases W with
    | done R => exact (IgnoredFieldPiObservation.compute (pending := []) heq hs hΓ hΓ H R).finish
  | cons x args ih =>
    change env.HasType univs Γ (VExpr.mkApps (.app f x) args) S at ht
    cases RX with
    | cons RImage RImages =>
      cases W with
      | @app _ rawA rawB image images _ RPi W =>
        obtain ⟨A, B, hA, hB, EA, EB, HBody⟩ :=
          (IgnoredFieldPiObservation.compute (pending := []) heq hs hΓ hΓ H RPi).selected_pi
        simp only [List.reverse_nil, List.nil_append] at hA hB EA EB HBody
        have hT := hf.isType henv hΓ
        obtain ⟨T', HT', ET'⟩ := proofErase_scoped_compute_realize
          (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT.choose_spec rfl rfl RPi
        have hPi := HasType.forallE hA.choose_spec hB.choose_spec
        have EPi : proofErase Γ (.forallE A B) = .forallE rawA rawB := by
          rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
            if_neg (not_isProof_of_sort hΓ hPi), EA, EB]
        obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HT'.hasType.2 hPi (ET'.trans EPi.symm)).2
          (not_isProof_of_sort hΓ HT'.hasType.2)
        have HE := HT'.toU.trans henv hΓ (HN.defeq hΓ)
        have hf' := hf.defeqU_r henv hΓ HE
        obtain ⟨V, hApp⟩ := spine_head_type (f := .app f x) hΓ ht
        obtain ⟨A₀, B₀, hf₀, hx₀⟩ := hApp.app_inv henv hΓ
        obtain ⟨⟨q, HA⟩, _⟩ := (hf₀.uniqU henv hΓ hf').forallE_inv henv hΓ
        have hx := HA.defeq hx₀
        obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize
          (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RImage
        have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
        have HS := IgnoredFieldPiObservation.supply (pending := []) hΓ hΓA HXY.hasType.2 HBody
        have EInst : proofErase Γ (B.inst y) = rawB.inst (proofErase Γ y) := by
          rw [proofErase_instN hΓA HXY.hasType.2 Ctx.InstN.zero hB.choose_spec, EB]
        have HEApp := IsDefEq.appDF hf' HXY
        have HEApps := spine_function_eq hΓ HEApp.toU ht
        have ht' := (HEApps.of_l henv hΓ ht).hasType.2
        apply ih (T := B.inst y) ?_ (hf'.app HXY.hasType.2) ht' RImages ?_
        · rw [EInst]
          exact HS
        · rwa [EInst, EY]

/-- A native application with a literal field-independent initial type has
its exact selected result reachable from the original lower result type.
Native recoveries of the head must retain this fixed type origin; this is
supplied by a literal constant or context declaration, not ordinary typing alone. -/
theorem static_structure_ignored_field_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.sort u))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls fields (g.liftN fields.length)))
    (hlen : fields.length = args.length)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) S)
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) rawF T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls fields (g.liftN fields.length))) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps rawF images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ g) out := by
  have hctx := (IsType.wrapForalls_inv henv hΓ (hf.isType henv hΓ)).1
  have HO := IgnoredFieldPiObservation.of_telescope (D := D) (pending := []) hΓ hg hctx
  have HO' : IgnoredFieldPiObservation D Γ g u args.length []
      (proofErase Γ (VExpr.wrapForalls fields (g.liftN fields.length))) := by
    simpa only [hlen, List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using HO
  obtain ⟨T, RF, W⟩ := RN.selected_supply
  exact HO'.supply_history heq hs hΓ hf ht RX (W.precompute (HN RF))


/-- A literal constant declaration supplies the fixed type origin for an
arbitrary dependent telescope whose result ignores its arguments. The entire
native history may convert between argument applications. This covers field
suffixes declared at the head; an arbitrary preceding parameter history is not
silently replaced by such a literal declaration. -/
theorem static_structure_declared_ignored_field_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.sort u))
    (hc : env.constants ctor = some ci) (hwc : ∀ l ∈ cls, l.WF univs)
    (hlc : cls.length = ci.uvars)
    (HT : ci.type.instL cls = VExpr.wrapForalls fields (g.liftN fields.length))
    (HA : TelInst env univs Γ fields args)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor cls) images) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ g) out := by
  have hf : env.HasType univs Γ (.const ctor cls)
      (VExpr.wrapForalls fields (g.liftN fields.length)) := HT ▸ HasType.const hc hwc hlc
  have ht := HasType.mkApps_of_tel hf HA
  have hct : env.HasType univs [] (.const ctor cls) (ci.type.instL cls) := .const hc hwc hlc
  obtain ⟨_, hcT⟩ := hct.isType henv (by trivial)
  have Ect := proofErase_closed_context ((henv.ordered.closedC hc).instL) hcT hΓ
  apply static_structure_ignored_field_native_origin heq hs hΓ hg hf HA.1.symm ht ?_ RX RN
  intro T RF
  have RC := RF.const_compute hc
  rwa [← Ect, HT] at RC

end Lean4Lean.VEnv.Strengthening
