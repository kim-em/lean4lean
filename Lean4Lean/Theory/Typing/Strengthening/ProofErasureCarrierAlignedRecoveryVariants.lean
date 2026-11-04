import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedComputeVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedProjectionRecovery

/-! # Native recovery across structural universe variants

Recovery follows both the changed term and the changed context. Its output may
vary structurally, including dependent projection parameters and preceding
fields. Computation simulation is explicit and is proved below for concrete
core computation. No arbitrary recovery or carrier-conversion premise is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private variant_app_inv variant_proj_inv variant_lam_inv variant_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPrimitiveVariants

namespace ProofShape
/-- Context variants give pointwise variants of the lifted variable oracle. -/
theorem StructuralVariant.contextOracle (H : List.Forall₂ StructuralVariant Δ Δ') :
    ∀ i, StructuralVariant (contextOracle Δ i) (contextOracle Δ' i) := by
  induction H with
  | nil => exact fun _ => .refl
  | cons HA _ ih =>
    intro i
    cases i with
    | zero => exact HA.liftN
    | succ i => exact (ih i).liftN

/-- Context-independent primitive paths forget their scope annotations. -/
theorem ScopedCompute.core_forget (H : ScopedCompute (fun _ => Step) Δ a b) :
    Compute Step a b := by
  induction H with
  | base H => exact .base H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
end ProofShape

variable [Params]

/-- Typed structural simulation of scoped computations, allowing the actual
contexts to differ structurally. This interface is discharged for the core below. -/
def StructuralVariantCompute (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' e e' T T' out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    env.HasType univs Γ e T → env.HasType univs Γ' e' T' →
    List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ') →
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out →
    StructuralVariant (proofErase Γ e) (proofErase Γ' e') →
    ∃ out', ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' e') out' ∧ StructuralVariant out out'

/-- The entire context-independent core satisfies typed structural simulation. -/
theorem structuralVariantCompute_core
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    StructuralVariantCompute (fun _ => ErasedIotaPrimitive D) := by
  intro Γ Γ' e e' T T' out hΓ hΓ' ht ht' _HΓ R V
  obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_compute_variant hs hlevels hcon R.core_forget
    hΓ hΓ' ht ht' rfl V
  exact ⟨out', R'.scoped (fun H => .base H), V'⟩

/-- Projection recipes preserve variants of universes, family arguments and
major terms simultaneously, including all preceding-field captures. -/
theorem proofErase_carrier_aligned_projection_type_full_variant
    (HT : ProjTele env univs family info ls doms result)
    (HT' : ProjTele env univs family info ls' doms' result')
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls')
    (hj : info.nparams + j < doms.length) (hj' : info.nparams + j < doms'.length)
    (Hargs : List.Forall₂ StructuralVariant args args') (Hm : StructuralVariant m m') :
    StructuralVariant (projectionType family info doms j hj args m)
      (projectionType family info doms' j hj' args' m') := by
  have HD := carrier_aligned_projection_telescope_levels HT HT' hw hw' he
  have HP : List.Forall₂ (LEquiv univs)
      (doms.take (info.nparams + j)).reverse (doms'.take (info.nparams + j)).reverse :=
    List.Forall₂.reverse.2 (List.forall₂_take HD _)
  have hΓ := HT.ctx _ (Nat.le_of_lt hj)
  obtain ⟨u, ht⟩ := HT.doms _ hj
  have H := proofErase_carrier_aligned_level_variant_context
    (List.forall₂_getElem HD _ hj hj') hΓ ht (StructureReplay.level_context henv hΓ HP)
  apply H.instOuter_pair
  apply (List.forall₂_take Hargs _).append'
  apply List.forall₂_of_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map]
  exact .proj Hm

private theorem native_type (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ A, env.HasType univs Γ e A ∧ proofErase Γ A = out := by
  obtain ⟨A, hA, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ (Ctx.LiftN.zero []) ht rfl
      (by simpa only [List.length_nil, ProofShape.liftN_zero] using R)
  exact ⟨A, hA, by simpa only [List.length_nil, ProofShape.liftN_zero] using EA⟩

private theorem native_family_levels (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const family ls) args)) : ∀ l ∈ ls, l.WF univs := by
  obtain ⟨A, hA, EA⟩ := native_type hstep hΓ ht R
  obtain ⟨_, hA⟩ := hA.isType henv hΓ
  obtain ⟨args₀, rfl, _⟩ := proofErase_const_spine_inv EA
  obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const family ls) args₀) from ⟨_, hA⟩).of_mkApps henv hΓ
  exact (StructureReplay.family_instance_levels hi hΓ hhead).1

omit [Params] in
private theorem variant_bvar_inv (H : StructuralVariant (.bvar i) b) : b = .bvar i := by
  cases H; rfl

omit [Params] in
private theorem variant_sort_inv (H : StructuralVariant (.sort u) b) :
    ∃ v, b = .sort v ∧ u ≈ v := by
  cases H with
  | refl => exact ⟨_, rfl, by rfl⟩
  | sort H => exact ⟨_, rfl, H⟩

/-- Native recovery preserves structural variants of both context and term.
Every recovery constructor is covered, including application and projection;
only the computation simulation interface remains explicit. -/
theorem proofErase_carrier_aligned_recovery_variant
    (hstep : ErasedScopedPrimitiveDescent Step) (hsim : StructuralVariantCompute Step)
    (R : ScopedTypeRecovery Step Δ a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = a)
    (HΓ : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ'))
    (V : StructuralVariant a (proofErase Γ' e')) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') (proofErase Γ' e') out' ∧
      StructuralVariant out out' := by
  induction R generalizing Γ Γ' e e' T T' with
  | @bvar Δ i =>
    have EE := variant_bvar_inv V
    exact ⟨_, EE ▸ .bvar, StructuralVariant.contextOracle HΓ _⟩
  | sort hu =>
    obtain ⟨v, Ev, HV⟩ := variant_sort_inv V
    obtain rfl := erase_sort_inv Ev
    have hw := ht'.sort_inv henv
    exact ⟨_, Ev ▸ .sort hw, .sort (VLevel.succ_congr HV)⟩
  | const hc hw hn =>
    have VC : StructuralVariant (ProofShape.mkApps (.const _ _) []) (proofErase Γ' e') := V
    obtain ⟨ls', args', EC, HL, HP⟩ := VC.constant_spine
    cases HP
    obtain rfl := erase_const_inv EC
    obtain ⟨_, hc', hw', hn'⟩ := ht'.const_inv henv hΓ'
    rw [hc] at hc'; cases hc'
    have htype := (HasType.const (Γ := []) hc hw hn).isType henv (by trivial)
    exact ⟨_, EC ▸ .const hc hw' hn',
      proofErase_carrier_aligned_level_variant (LEquiv.instL_expr _ hw hw' HL) (by trivial) htype.choose_spec⟩
  | lam R ih =>
    obtain ⟨D, c, EV, VA, Vb⟩ := variant_lam_inv V
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨D', c', rfl, _, ED, Ec⟩ := erase_lam_inv EV
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨⟨v, hD⟩, _, hc⟩ := ht'.lam_inv henv hΓ'
    obtain ⟨C, RC, VC⟩ := ih (Γ := A :: Γ) (Γ' := D' :: Γ') ⟨hΓ, u, hA⟩ ⟨hΓ', v, hD⟩ hb hc
      (by simp only [proofEraseCtx, EA, EΓ]) Eb
      (by simpa only [proofEraseCtx, ED] using List.Forall₂.cons VA HΓ) (by simpa only [Ec] using Vb)
    exact ⟨_, by simpa only [EV, ED, Ec] using ScopedTypeRecovery.lam RC, .forallE VA VC⟩
  | app R ih =>
    obtain ⟨g, y, EV, Vf, Vx⟩ := variant_app_inv V
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨g', y', rfl, _, Eg, Ey⟩ := erase_app_inv EV
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨_, _, hg, _⟩ := ht'.app_inv henv hΓ'
    obtain ⟨G, RG, VG⟩ := ih hΓ hΓ' hf hg EΓ Ef HΓ (by simpa only [Eg] using Vf)
    obtain ⟨D, C, rfl, _, VC⟩ := variant_forallE_inv VG
    exact ⟨_, by simpa only [EV, Eg, Ey] using ScopedTypeRecovery.app (a := proofErase Γ' y') RG,
      VC.inst_pair Vx⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨D, C, EV, VA, VB⟩ := variant_forallE_inv V
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨D', C', rfl, _, ED, EC⟩ := erase_forallE_inv EV
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨⟨v, hD⟩, _, hC⟩ := ht'.forallE_inv henv
    obtain ⟨D₁, RD, VD⟩ := ihA hΓ hΓ' hA hD EΓ EA HΓ (by simpa only [ED] using VA)
    obtain ⟨C₁, RC, VC⟩ := ihB (Γ := A :: Γ) (Γ' := D' :: Γ') ⟨hΓ, u, hA⟩ ⟨hΓ', v, hD⟩ hB hC
      (by simp only [proofEraseCtx, EA, EΓ]) EB
      (by simpa only [proofEraseCtx, ED] using List.Forall₂.cons VA HΓ) (by simpa only [EC] using VB)
    obtain ⟨v₁, rfl, HD⟩ := variant_sort_inv VD
    obtain ⟨v₂, rfl, HC⟩ := variant_sort_inv VC
    exact ⟨_, by simpa only [EV, ED, EC] using ScopedTypeRecovery.forallE RD RC,
      .sort (VLevel.imax_congr HD HC)⟩
  | proj hi HT hj hlen R ih =>
    rename_i Δ mraw s info ls doms result j args
    obtain ⟨m', EV, Vm⟩ := variant_proj_inv V
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨n, rfl, _, En⟩ := erase_proj_inv EV
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _⟩ := ht'.proj_inv henv hΓ'
    obtain ⟨N, RN, VN⟩ := ih hΓ hΓ' hm.hasType.2 hn.hasType.2 EΓ Em HΓ (by simpa only [En] using Vm)
    obtain ⟨ls', args', EN, HL, HP⟩ := VN.constant_spine
    rw [EN] at RN
    have hw := native_family_levels hstep hi hΓ hm.hasType.2 (by simpa only [EΓ, Em] using R)
    have hw' := native_family_levels hstep hi hΓ' hn.hasType.2 RN
    obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi hw'
    have hj' : info.nparams + j < doms'.length := by have := HT.numFields; have := HT'.numFields; omega
    refine ⟨_, ?_, proofErase_carrier_aligned_projection_type_full_variant HT HT' hw hw' HL hj hj' HP Vm⟩
    simpa only [EV, En] using ScopedTypeRecovery.proj hi HT' hj' (HP.length_eq.symm.trans hlen) RN
  | convert R RC ih =>
    obtain ⟨N, RN, VN⟩ := ih hΓ hΓ' ht ht' EΓ Ee HΓ V
    obtain ⟨A, hA, EA⟩ := native_type hstep hΓ ht (by simpa only [EΓ, Ee] using R)
    obtain ⟨B, hB, EB⟩ := native_type hstep hΓ' ht' RN
    obtain ⟨_, hA⟩ := hA.isType henv hΓ
    obtain ⟨_, hB⟩ := hB.isType henv hΓ'
    obtain ⟨out', RB, VB⟩ := hsim hΓ hΓ' hA hB (by simpa only [EΓ] using HΓ)
      (by simpa only [EΓ, EA] using RC)
      (by simpa only [EA, EB] using VN)
    exact ⟨out', RN.convert (by simpa only [EB] using RB), VB⟩

end Lean4Lean.VEnv.Strengthening
