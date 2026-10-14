import Lean4Lean.Theory.Typing.Strengthening.FamilyHeadRepair
import Lean4Lean.Theory.Typing.Strengthening.RecoveryReplay

/-! # Compile eta-containing head traces into type recovery

These rules accept the existing constructor observation model's mixed paths,
whose eta annotations need not themselves have recovery certificates. Backwards
observations first repair the path into pattern computation. A computational
base containing pattern computation can then recover the exposed head directly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute)
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- Repair a Pi-exposing mixed path before converting the inferred type. This
needs no recovery of the original path's intermediate eta annotations. -/
theorem TypeRecoveryWith.pi_of_eta_trace (R : TypeRecoveryWith C Γ f T)
    (hbase : ∀ {Γ e out}, PatternCompute D e out → C Γ e out)
    (hD : ConstructorObservation.ConstructorRigid D)
    (HT : ConstructorObservation.EtaCompute D T (.forallE A B)) :
    ∃ A' B', TypeRecoveryWith C Γ f (.forallE A' B') := by
  obtain ⟨A', B', RC⟩ := HT.pi_exposure hD
  exact ⟨A', B', .convert R (hbase RC)⟩

/-- A repaired family trace supplies a projection recovery. Source typing and
ambient replay derive field selection for the new parameters; no preservation
of the trace's original arguments or selected output is required. -/
theorem TypeRecoveryWith.proj_of_eta_trace (R : TypeRecoveryWith C Γ m T)
    (hbase : ∀ {Γ e out}, PatternCompute D e out → C Γ e out)
    (hc : ComputeReplay C) (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : VExpr.WF env univs Γ (.proj s i m))
    (HT : ConstructorObservation.EtaCompute D T (mkApps (.const s ls) args)) :
    ∃ F, TypeRecoveryWith C Γ (.proj s i m) F := by
  obtain ⟨args', RC, _⟩ := HT.family_exposure hD hi
  have R' : TypeRecoveryWith C Γ m (mkApps (.const s ls) args') := .convert R (hbase RC)
  obtain ⟨_, ht'⟩ := ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
    HasType.proj_inv henv hΓ ht'
  have hm' := R'.hasType_of_replay hc hΓ ⟨_, hm.hasType.2⟩
  obtain ⟨F, hF⟩ := projection_recovered_field_exists henv hΓ hi ⟨_, ht'⟩ hm'
  exact ⟨F, .proj hi R' hF⟩

end Lean4Lean.VEnv.Strengthening
