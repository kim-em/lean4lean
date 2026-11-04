import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation

/-! # Computation squares for statically masked structure eta

The output of structure expansion is functorial in its parameters and source:
proof fields remain erased and data projections compute with their source.
A source-change peak therefore joins if both endpoints have native family
recovery and the parameter spines compute to the second selected spine.
The second recovery is an explicit premise, not a completeness assertion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Source computation lifts through every retained field of the expansion. -/
theorem ProofShape.nativeStructureField_compute
    (R : ScopedCompute Step Δ a b) :
    ScopedCompute Step Δ (nativeStructureField family info ls a j)
      (nativeStructureField family info ls b j) := by
  classical
  unfold nativeStructureField
  split
  · exact .refl
  · exact .proj R

/-- Structure output commutes with simultaneous parameter and source
computation. Dependent fields use the same closed mask at both endpoints. -/
theorem ProofShape.nativeStructureOutput_compute
    (RP : List.Forall₂ (ScopedCompute Step Δ) ps qs)
    (R : ScopedCompute Step Δ a b) :
    ScopedCompute Step Δ (nativeStructureOutput family info ls ps a)
      (nativeStructureOutput family info ls qs b) := by
  unfold nativeStructureOutput
  apply ScopedCompute.mkApps .refl
  apply List.Forall₂.append RP
  apply List.forall₂_map_left_iff.2
  apply List.forall₂_map_right_iff.2
  induction List.range info.numFields with
  | nil => exact .nil
  | cons j js ih => exact .cons (nativeStructureField_compute R) ih

/-- A finite-union structure-eta/source-change peak joins at the second
endpoint's expansion when both native family guards are available. Only the
second guard and parameter computation remain to be obtained in a general
source-stability argument; no original equality is used as a raw guard. -/
theorem static_structure_eta_source_square
    (hi : env.projections family info) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hp : ps.length = info.nparams) (hq : qs.length = info.nparams)
    (RA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ a
      (ProofShape.mkApps (.const family ls) ps))
    (RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ b
      (ProofShape.mkApps (.const family ls) qs))
    (RP : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) ps qs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a
        (nativeStructureOutput family info ls ps a) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (nativeStructureOutput family info ls ps a) (nativeStructureOutput family info ls qs b) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ b
        (nativeStructureOutput family info ls qs b) := by
  exact ⟨.base (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hp RA)),
    nativeStructureOutput_compute RP R,
    .base (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hq RB))⟩

end Lean4Lean.VEnv.Strengthening
