import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionParameterCut

/-! # Native constructor outputs with retained function arguments

The dependent application theorem uses observed beta substitution. A constructor
head's original-header history is an explicit premise here; the registered
head-expansion wrapper below discharges it from actual declaration data.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom)
variable [Params] [Atom]

/-- Native application exposes its selected Pi before substituting the current
argument. Original-header ancestry and the finite argument observation suffice
for every native conversion tail and subsequent result-type computation. -/
theorem pending_function_native_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (hΓ : OnCtx Γ (env.IsType univs)) (HV : V.Typed (proofEraseCtx Γ))
    (HP : Obs info.ctorName r v (proofEraseCtx Γ) V p (.arrow .atom .atom) (.app [] .pi))
    (HH : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    Obs info.ctorName r v (proofEraseCtx Γ) V out (.sort v) .pi := by
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  exact pending_function_pi_observation heq hs hi hz EA hD hS hr hDr hF hΓ HV HP
    (HH RF) RX (RC.trans RT)

/-- Computational interpretation turns the observed native result into one
fixed family output. The free-variable realizations are explicit, and the
selected family exposure is the actual single closed certificate from the
preceding return theorem. No native certificate for p or a is assumed. -/
theorem pending_function_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs)) (HV : V.Typed (proofEraseCtx Γ))
    (HP : Obs info.ctorName r v (proofEraseCtx Γ) V p (.arrow .atom .atom) (.app [] .pi))
    (HW : ∀ i t key, V i t key → WorldComputes (ErasedStaticStructureEtaExpansionUnion D)
      (selectedCanonical info.ctorName r A) (proofEraseCtx Γ) (.bvar i) t key)
    (HH : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam A (.const info.ctorName []))) := by
  have H := pending_function_native_observation heq hs hi hz EA hD hS hr hDr hF hΓ HV HP HH RX RN RT
  have hF' : env.HasType univs [] (.const r [])
      (AtomicControl.ControlType.arrow (.arrow .atom .atom) (.sort v)).expr := by
    simpa only [AtomicControl.ControlType.expr, EA] using hF
  obtain ⟨HC, HA⟩ := closed_selected_header heq hs hF' RF
  have HR := H.world_computes (union_world_rename heq hs) (fun t τ => selectedCanonical_subst HA t)
    (target := selectedCanonical info.ctorName r A) rfl
    (fun HF => family_world_selected heq hs HF (selected_family_native_world heq hs HC RF))
    ContextRenaming.identity.interpretation (σ := Subst.id) HW
  simpa only [ProofShape.subst_id, WorldComputes, selectedCanonical] using HR

/-- A supplied constant function needs only ordinary typing at Unit -> Unit.
Its literal annotation L may differ from Unit and contain ambient variables.
No original or current native argument certificate is required; the empty free
valuation and terminal body discharge all computational realization premises. -/
theorem constant_function_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HL : AtomicControl.ControlTyping (proofEraseCtx Γ) (.lam L (.const info.ctorName [])) (.arrow .atom .atom))
    (HH : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam L (.const info.ctorName [])) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam A (.const info.ctorName []))) := by
  have HP : Obs info.ctorName r v (proofEraseCtx Γ) (fun _ _ _ => False)
      (.lam L (.const info.ctorName [])) (.arrow .atom .atom) (.app [] .pi) :=
    .lam HL (by simp) (.terminal HL.lam_parts.1)
  exact pending_function_native_return heq hs hi hz EA hD hS hr hDr hF RF hΓ
    (by intro i t key H; cases H) HP (by intro i t key H; cases H) HH RX RN RT

/-- The one retained free function demand used by concrete lookup examples. -/
def FunctionSets (i : Nat) : AtomicControl.Sets :=
  fun j t key => j = i ∧ t = .arrow .atom .atom ∧ key = .app [] .pi

/-- Actual lookup initializes ordinary typing, the finite observation, and
native recovery at the literal original function type. This is used only to
initialize a free-variable realization, not to recover the current argument. -/
theorem function_lookup
    (EA : Atom.type = .const s [])
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s []))) :
    (FunctionSets i).Typed (proofEraseCtx Γ) ∧
    Obs c r v (proofEraseCtx Γ) (FunctionSets i) (.bvar i) (.arrow .atom .atom) (.app [] .pi) ∧
    ScopedTypeRecovery Step (proofEraseCtx Γ) (.bvar i) (.forallE (.const s []) (.const s [])) := by
  have hx : env.HasType univs Γ (.bvar i) (AtomicControl.ControlType.arrow .atom .atom).expr := by
    simpa only [AtomicControl.ControlType.expr, EA] using HasType.bvar hl
  have hn := AtomicControl.ControlType.not_isProof hΓ hx
  have EX : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have HX : AtomicControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.arrow .atom .atom) :=
    ⟨Γ, _, hΓ, rfl, hx, EX⟩
  refine ⟨?_, .var HX (.fn (by simp) .atom) ⟨rfl, rfl, rfl⟩, ?_⟩
  · rintro j t key ⟨rfl, rfl, rfl⟩; exact HX
  · have RR := proofErase_scoped_lookup_recovery (Step := Step) hΓ hl hn .refl
    rwa [EX, unit_arrow_erasure hS hΓ] at RR

omit [Atom] in
/-- A retained function lookup may compute arbitrarily before it is supplied.
Every subsequent native result returns to the selected family instance. Only
the constructor head's ancestry remains an explicit premise in this wrapper. -/
theorem lookup_function_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (HH : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam A (.const info.ctorName []))) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  obtain ⟨HV, HP, R₀⟩ := function_lookup (c := info.ctorName) (r := r) (v := v)
    (Step := ErasedStaticStructureEtaExpansionUnion D) rfl hS hΓ hl
  exact pending_function_native_return heq hs hi hz rfl hD hS hr hDr hF RF hΓ HV HP
    (by
      rintro j t key ⟨rfl, rfl, rfl⟩
      exact native_unit_function_world_of_target heq hs hi hp hx hz R₀ rfl)
    HH RX RN RT

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
