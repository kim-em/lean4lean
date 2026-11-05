import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitIdentityTypeHistory

/-! # Native expansions and canonical types of observed constructor controls

The richer observer accepts all previously constructed historical frames and
preserves native identity creation and functional eta. Complete compatible beta
reduction retains the observer and the canonical unit-family native readout.
Full enriched computation of constructor prefixes is not yet covered.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

namespace ConstructorControlObservation

/-- Native identity creation records the selected recursive type history.
The annotation may be a computed higher-order type, not a literal family. -/
theorem Obs.native_identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : Obs D Γ r info origin n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ origin n Δ S)
    (R : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ r info origin n Δ S out o := by
  cases R with
  | intro RN =>
    have HN := H.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS RN
    obtain ⟨u, _, SD⟩ := HN.sort_witness (fun H => H.sort_witness)
    apply Obs.app (keys := [o])
    · apply Obs.lam SD
      · intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact HN
      · exact .var (by simp [PureObservation.Sets.cons])
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact H

/-- Functional eta preserves higher-order demands with retained data results.
Only demanded fresh arguments must be retained; ignored inputs may be proofs.
This theorem concerns functional demands, not eta on ground data payloads. -/
theorem Obs.native_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : Obs D Γ r info origin n Δ S raw (.app keys result))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ origin n Δ S)
    (R : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ r info origin n Δ S out (.app keys result) := by
  cases R with
  | intro RN SD =>
    have HN := H.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS RN
    have HD := HN.function_parts.1
    apply Obs.lam SD HD
    apply Obs.app (H.lift SD)
    intro key hk
    have E : etaArgument _ = .bvar 0 :=
      if_neg ((HD key hk).sort_ne_zero (fun H => H.sort_witness) SD)
    rw [E]
    exact .var hk

/-- The earlier constructor/frame invariant supplies a genuine observation
of every nested frame. No extra term-observation premise is needed for entry. -/
theorem Obs.of_frame_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFrameHistory D Γ r info origin source) :
    Obs D Γ r info origin 0 (proofEraseCtx Γ) (fun _ _ => False) source .pi := by
  induction H with
  | payload H => exact .payload (H.type_payload heq hs hΓ hi hp hx)
  | constant _ ih =>
    exact ih.constant_expansion ⟨Γ, .sort (.succ .zero), hΓ, rfl,
      HasType.sort (by trivial), if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))⟩
  | @identity source A H HT RO ih =>
    have HA := (ConstructorFrameHistory.identity H HT RO).lower_type_history heq hs hΓ hi hp hx HH
      (raw_identity_native A source)
    obtain ⟨u, _, SD⟩ := HA.sort_witness
    apply Obs.app (keys := [.pi])
    · apply Obs.lam SD
      · intro key hk
        obtain rfl := List.mem_singleton.1 hk
        simpa only [LowerTypeDemand, NativeGroundDemand] using HA
      · exact .var (by simp [PureObservation.Sets.cons])
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact ih

end ConstructorControlObservation

/-- Every native selection from an observed data control program returns to
the canonical unit-family type. The observation can contain arbitrary nested
applications and lambdas, with constructor fields dependent on their binders. -/
theorem constructor_control_unit_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (ht : env.HasType univs Γ e T)
    (H : ConstructorControlObservation.Obs D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ e) .pi)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have HO : LowerTypeHistory D Γ (proofErase Γ (.app (.const r []) (.bvar i)))
      0 (proofEraseCtx Γ) out := by
    simpa only [LowerTypeDemand, NativeGroundDemand] using
      H.native heq hs hΓ hR hrp hrx HH hΓ (Ctx.LiftN.zero []) ht rfl rfl (fun _ _ h => h.elim) RN
  exact HO.unit_family_return heq hs hi hp hx hz hD hS (henv.projectionRigid hR) hDr hΓ hF hl

/-- After arbitrary compatible beta computation of the observed program,
every selected native type still returns canonically. Native conversion tails
may use the complete enriched language. The major path here is beta, not an
assertion of preservation through all enriched constructor-prefix computation. -/
theorem constructor_control_beta_unit_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (ht : env.HasType univs Γ e T)
    (H : ConstructorControlObservation.Obs D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ e) .pi)
    (RB : BetaRed (proofErase Γ e) target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) target out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have HO := H.beta_compute heq hs hΓ RB hΓ (Ctx.LiftN.zero []) ht rfl rfl (fun _ _ h => h.elim)
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl rfl (.beta RB)
  exact constructor_control_unit_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
    hΓ hF hl HE.hasType.2 (Ee' ▸ HO) (Ee' ▸ RN)

end Lean4Lean.VEnv.Strengthening
