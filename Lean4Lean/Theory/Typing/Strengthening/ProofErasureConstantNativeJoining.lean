import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedSupplyJoining
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedConstructorFamily

/-! # Joining all selected native outputs of typed constant spines

The fixed stored constant type anchors every selected history. Under type-only
fork joining, arbitrary conversions and argument supply retain output joining.
For registered constructors, an argumentwise realization also supplies the raw
family recovery even when the constructor term itself is proof-valued.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private spine_head_type spine_function_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params] {D : PureObservation.Definitions}

/-- All native outputs of the same constant spine with independently computed
ordinary arguments join under TypeForkJoin. Every recovery starts at the actual
stored header; no directed/common header condition or native argument premise
is required. The original whole constant application may be a proof. -/
theorem TypeForkJoin.constant_native_outputs_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = ci.uvars)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const c ls) args) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) images) left)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) images) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨L, NL, WL⟩ := RL.selected_supply
  obtain ⟨R, NR, WR⟩ := RR.selected_supply
  have PL := NL.const_compute hc
  have PR := NR.const_compute hc
  have hfc : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨u, hT⟩ := hfc.isType henv (by trivial)
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ
  rw [← EC] at PL PR
  have hf : env.HasType univs Γ (.const c ls) (ci.type.instL ls) := .const hc hw hl
  exact HF.selected_supply_join heq hs hΓ hf hf ht RX ScopedCompute.refl ScopedCompute.refl
    (WL.precompute PL) (WR.precompute PR)

/-- Realize independent argument computations while preserving the typing of
the whole application. This works for proof-valued applications as well: only
the individual arguments, not the erased whole spine, are replayed. -/
theorem proofErase_computed_spine_arguments_realize
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T)
    (RX : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images) :
    ∃ args', env.IsDefEq univs Γ (VExpr.mkApps f args) (VExpr.mkApps f args') T ∧
      args'.map (proofErase Γ) = images := by
  induction args generalizing f images with
  | nil => cases RX; exact ⟨[], ht, rfl⟩
  | cons x args ih =>
    change env.HasType univs Γ (VExpr.mkApps (.app f x) args) T at ht
    cases RX with
    | cons RX RArgs =>
      obtain ⟨S, hApp⟩ := spine_head_type hΓ ht
      obtain ⟨A, B, hf, hx⟩ := hApp.app_inv henv hΓ
      obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize hstep hΓ hx rfl rfl RX
      have HE := (spine_function_eq hΓ (IsDefEq.appDF hf HXY).toU ht).of_l henv hΓ ht
      obtain ⟨ys, HY, EYS⟩ := ih HE.hasType.2 RArgs
      exact ⟨y :: ys, HE.trans HY, by simp only [List.map_cons, EY, EYS]⟩

/-- Computed argument images supply a raw constructor's exact family guard,
including proof-valued constructors. The source relation needs descent only;
the target native relation is arbitrary. No family-header alignment or native
argument certificate occurs. -/
theorem computed_raw_structure_constructor_family
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) args) T)
    (RX : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images)
      (ProofShape.mkApps (.const s ls) (images.take info.nparams)) := by
  obtain ⟨args', HE, EArgs⟩ := proofErase_computed_spine_arguments_realize hstep hΓ ht RX
  have hlen' : args'.length = info.nparams + info.numFields := by
    have H₁ := congrArg List.length EArgs
    have H₂ := RX.length_eq
    simp only [List.length_map] at H₁ H₂
    omega
  have HW := structure_constructor_native_walk hΓ hi hx hlen' HE.hasType.2
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, HE.hasType.2⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have hc : env.HasType univs [] (.const info.ctorName ls) (info.ctorType.instL ls) :=
    .const (henv.ordered.projectionConstructor hi) hw hl
  obtain ⟨u, hType⟩ := hc.isType henv (by trivial)
  have hHead := hc.weak0 henv.ordered (Γ := Γ)
  have HS := proofErase_native_supply hΓ (hType.weak0 henv.ordered) HW
  rw [proofErase_closed_context ((henv.ordered.closedC
    (henv.ordered.projectionConstructor hi)).instL) hType hΓ] at HS
  have RN := (ScopedTypeRecovery.const (Step := Target) (Δ := proofEraseCtx Γ)
    (henv.ordered.projectionConstructor hi) hw hl).supply HS
  obtain ⟨v, hFamily⟩ := (native_walk_typing hHead HW).isType henv hΓ
  rw [proofErase_const_spine hΓ hFamily (not_isProof_of_sort hΓ hFamily)] at RN
  simpa only [List.map_take, EArgs] using RN

omit [Params] in
private theorem forall₂_take (R : List.Forall₂ P xs ys) (n : Nat) :
    List.Forall₂ P (xs.take n) (ys.take n) := by
  induction R generalizing n with
  | nil => simp
  | cons h R ih =>
    cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

/-- Under type-only fork joining, every selected native output of a registered
unindexed constructor joins its original family. Parameters and fields may
compute independently; their native certificates and all header-alignment
conditions are absent. Unlike exact ancestry, the conclusion retains a common
reduct and covers histories that branch before any proposed checkpoint. -/
theorem TypeForkJoin.registered_constructor_output_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) args) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const s ls) ((args.take info.nparams).map (proofErase Γ))) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  have RF := computed_raw_structure_constructor_family
    (Target := ErasedStaticStructureEtaExpansionUnion D)
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hi hx hlen ht RX
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  obtain ⟨shared, LF, RO⟩ := HF.constant_native_outputs_join heq hs hΓ hci hw hl ht RX RF RN
  have RP : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((args.take info.nparams).map (proofErase Γ)) (images.take info.nparams) := by
    simpa only [List.map_take] using forall₂_take RX info.nparams
  exact ⟨shared, (ScopedCompute.mkApps ScopedCompute.refl RP).trans LF, RO⟩

/-- A pivot recovering the original family shares a native output with every
computed constructor history. This is common-output transfer, not the false
claim that the original family computes to each exact selected output. -/
theorem TypeForkJoin.registered_constructor_common_transfer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) args) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot
      (ProofShape.mkApps (.const s ls) ((args.take info.nparams).map (proofErase Γ))))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images) out) :
    ∃ shared, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  obtain ⟨shared, RF, RO⟩ := HF.registered_constructor_output_join heq hs hΓ hi hx hlen ht RX RN
  exact ⟨shared, RP.convert RF, RO⟩

end Lean4Lean.VEnv.Strengthening
