import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedContextConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Semantic head exposure as an input to contextual recovery

Only sorts, Pis, and registered family heads are demanded. Their arguments
and annotations are freely selected by computation. This suffices for recovery
existence and conversion of structural subsingletons, including Pi telescopes. The exposure premise is
unproved for the full joint union; this file does not assume exact recovery
at arbitrary assigned types or claim a smaller sufficient strengthening front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

private theorem compute_eq
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ U)) :
    env.IsDefEqU univs Γ T U := by
  obtain ⟨V, HTV, EV⟩ := proofErase_scoped_compute_realize hstep hΓ hT rfl rfl R
  obtain ⟨_, HVU⟩ := (proofErase_reflect hΓ HTV.hasType.2 hU EV).2
    (not_isProof_of_sort hΓ HTV.hasType.2)
  exact IsDefEqU.trans henv hΓ ⟨_, HTV⟩ (HVU.defeq hΓ)

/-- Missing computational head adequacy for typed convertible types. The
computed Pi or family may have different annotations, universes and arguments.
Outputs have actual typed representatives; no comparison of their full syntax
with the requested type is part of this premise. -/
structure ScopedSemanticHeadExposure
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop where
  sort : ∀ {Γ T u v}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ T (.sort u) → env.IsDefEqU univs Γ T (.sort v) →
    ∃ w, ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) (.sort w)
  pi : ∀ {Γ T u A B}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ T (.sort u) → env.IsDefEqU univs Γ T (.forallE A B) →
    ∃ D C, env.HasType univs Γ (.forallE D C) (.sort u) ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T)
        (proofErase Γ (.forallE D C))
  family : ∀ {Γ T u s info ls args}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ T (.sort u) → env.projections s info →
    env.IsDefEqU univs Γ T (VExpr.mkApps (.const s ls) args) →
    ∃ ls' args', env.HasType univs Γ (VExpr.mkApps (.const s ls') args') (.sort u) ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T)
        (proofErase Γ (VExpr.mkApps (.const s ls') args'))

/-- An existing recovery can expose a sort whenever the expression is
sort-typed. Its selected universe is not required to match the assigned syntax. -/
theorem ScopedSemanticHeadExposure.recover_sort
    (hstep : ErasedScopedPrimitiveDescent Step) (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ v, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.sort v) := by
  obtain ⟨T, heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ he R
  obtain ⟨_, hT⟩ := heT.isType henv hΓ
  obtain ⟨v, RT⟩ := H.sort hΓ hT (heT.uniqU henv hΓ he)
  exact ⟨v, R.convert (ET ▸ RT)⟩

/-- An existing recovery can expose some Pi at a function-typed expression.
This retains actual source typing without comparing the two Pi annotations. -/
theorem ScopedSemanticHeadExposure.recover_pi
    (hstep : ErasedScopedPrimitiveDescent Step) (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ D C, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.forallE D C) := by
  obtain ⟨T, heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ he R
  obtain ⟨_, hT⟩ := heT.isType henv hΓ
  obtain ⟨D, C, hPi, RT⟩ := H.pi hΓ hT (heT.uniqU henv hΓ he)
  have HR := R.convert (ET ▸ RT)
  rw [show proofErase Γ (.forallE D C) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at HR
  exact ⟨_, _, HR⟩

/-- Family exposure selects a registered major type and reconstructs its
ordinary typing. The parameters and universes need not be the assigned ones. -/
theorem ScopedSemanticHeadExposure.recover_family
    (hstep : ErasedScopedPrimitiveDescent Step) (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (he : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ ls' args', env.HasType univs Γ e (VExpr.mkApps (.const s ls') args') ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
        (proofErase Γ (VExpr.mkApps (.const s ls') args')) := by
  obtain ⟨T, heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ he R
  obtain ⟨_, hT⟩ := heT.isType henv hΓ
  obtain ⟨ls', args', hF, RT⟩ := H.family hΓ hT hi (heT.uniqU henv hΓ he)
  have HE := compute_eq hstep hΓ hT hF RT
  exact ⟨ls', args', (HE.of_l henv hΓ hT).defeq heT, R.convert (ET ▸ RT)⟩

/-- The three semantic head clauses suffice to recover some type of every
retained expression, by structural induction on its actual syntax. Projection
recovery uses the exposed major's registered telescope. This asserts no exact
recovery of a chosen convertible type and no comparison completeness. -/
theorem ScopedSemanticHeadExposure.recovery_exists
    (hstep : ErasedScopedPrimitiveDescent Step) (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hn : ¬ IsProof Γ e) :
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out := by
  induction e generalizing Γ T with
  | bvar i =>
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
    exact ⟨_, .bvar⟩
  | sort u =>
    rw [show proofErase Γ (.sort u) = .sort u from if_neg hn]
    exact ⟨_, .sort (HasType.sort_inv henv.ordered ht)⟩
  | const c ls =>
    obtain ⟨ci, hc, hw, hl⟩ := HasType.const_inv henv hΓ ht
    rw [show proofErase Γ (.const c ls) = .const c ls from if_neg hn]
    exact ⟨_, .const hc hw hl⟩
  | lam A b _ ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨B, R⟩ := ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (fun hp => hn (hp.lam hΓ hA))
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact ⟨_, .lam R⟩
  | app f a ihf _ =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨_, R⟩ := ihf hΓ hf (not_isProof_fn hΓ hf ha hn)
    obtain ⟨D, C, R⟩ := H.recover_pi hstep hΓ hf R
    rw [show proofErase Γ (.app f a) = .app _ _ from if_neg hn]
    exact ⟨_, .app R⟩
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨_, RA⟩ := ihA hΓ hA (not_isProof_of_sort hΓ hA)
    obtain ⟨_, RB⟩ := ihB hΓA hB (not_isProof_of_sort hΓA hB)
    obtain ⟨u', RA⟩ := H.recover_sort hstep hΓ hA RA
    obtain ⟨v', RB⟩ := H.recover_sort hstep hΓA hB RB
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg hn]
    exact ⟨_, .forallE RA RB⟩
  | proj s j m ihm =>
    obtain ⟨info, ls, ps, idx, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, R⟩ := ihm hΓ hm.hasType.2 (not_isProof_major hΓ ht hn)
    obtain ⟨ls', args', hmF, RF⟩ := H.recover_family hstep hΓ hi hm.hasType.2 R
    obtain ⟨u, hF⟩ := hmF.isType henv hΓ
    obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const s ls') args') from
      ⟨_, hF⟩).of_mkApps henv hΓ
    obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ hhead
    obtain ⟨doms, result, HT⟩ := projection_telescope_exists hi hw
    obtain ⟨hj, F, hpj, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT ht hn hmF
    rw [proofErase_const_spine hΓ hF (not_isProof_of_sort hΓ hF)] at RF
    have hlen := StructureReplay.family_arity henv hΓ hi ⟨u, hF⟩
    refine ⟨projectionType s info doms j hj (args'.map (proofErase Γ)) (proofErase Γ m), ?_⟩
    rw [show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg hn]
    exact ScopedTypeRecovery.proj hi HT hj (by simpa only [List.length_map] using hlen) RF

/-- Semantic head exposure transports every structural subsingleton carrier
through ordinary type conversion, including arbitrary Pi telescopes. The
output is a computation to another structural subsingleton, not just a guard.
In the Pi case, only the smaller codomain induction changes binder contexts;
primitive context transport moves its resulting computation. No comparison or
carrier-conversion closure is assumed. -/
theorem ScopedSemanticHeadExposure.subsingleton_conversion
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HE : env.IsDefEqU univs Γ T U)
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    ∃ out, ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ U) out ∧ SubsingletonCarrier out := by
  generalize E : proofErase Γ T = rawT at HS
  induction HS generalizing Γ T U u v with
  | unit hi hx hf hp =>
    obtain ⟨args, rfl, EA⟩ := proofErase_const_spine_inv E
    obtain ⟨ls', args', hF, RF⟩ := H.family hΓ hU hi HE.symm
    have hlen := StructureReplay.family_arity henv hΓ hi ⟨_, hF⟩
    rw [proofErase_const_spine hΓ hF (not_isProof_of_sort hΓ hF)] at RF
    exact ⟨_, RF, .unit hi hx hf (by simpa only [List.length_map, hx, Nat.add_zero] using hlen)⟩
  | forallE HS ih =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv E
    obtain ⟨⟨w, hA⟩, _, hB⟩ := hT.forallE_inv henv
    obtain ⟨D, C, hPi, RP⟩ := H.pi hΓ hU HE.symm
    have HPi := HE.trans henv hΓ (compute_eq hstep hΓ hU hPi RP)
    obtain ⟨⟨_, HAD⟩, _, HBC⟩ := HPi.forallE_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
    obtain ⟨out, RC, HC⟩ := ih hΓA HBC.hasType.1 HBC.hasType.2 ⟨_, HBC⟩ EB
    have W : IsDefEqCtx env univs Γ (A :: Γ) (D :: Γ) := .succ .zero HAD
    have RC := RC.defeqCtx hsubst hΓ W
    rw [proofErase_defeqCtx hΓA W HBC.hasType.2] at RC
    rw [show proofErase Γ (.forallE D C) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi)] at RP
    exact ⟨_, RP.trans (.forallE .refl RC), .forallE HC⟩

/-- Every guard supplied by a structural subsingleton survives arbitrary type
conversion under the head-exposure premise. Endpoint syntax is unrestricted;
ordinary typings are required only when interpreting this raw guard soundly. -/
theorem ScopedSemanticHeadExposure.subsingleton_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HE : env.IsDefEqU univs Γ T U) (HS : SubsingletonCarrier (proofErase Γ T)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ U) a b := by
  obtain ⟨out, R, HS⟩ := H.subsingleton_conversion hstep hsubst hΓ hT hU HE HS
  exact .carrierCompute R (.carrierSubsingleton HS)

end Lean4Lean.VEnv.Strengthening
