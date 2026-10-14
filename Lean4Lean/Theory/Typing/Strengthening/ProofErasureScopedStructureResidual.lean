import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.RegisteredStructureEquations

/-! # Structure-eta residual guards after computation of the expansion

Constructor rigidity exposes a separate computation of every parameter and
field. A visible field originally is a projection of the unchanged short major;
its computation supplies the recursive residual guard directly. Hidden proof
fields stay hidden. No computational confluence premise is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Computing a literal structure-eta expansion leaves a recursive field guard
against the unchanged short major. No raw endpoint representatives are needed.
Only actual constructor-head exclusion and proof-marker fixedness are used. -/
theorem ScopedCompute.structure_eta_residual
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hctor : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const info.ctorName ls) args) out)
    (H : StructureEtaHead a m) (R : ScopedCompute Step Δ a out) :
    ScopedCompare Step Δ true out m := by
  cases H with
  | @intro family info ls ps fields m hi hx hp hf hadm Hfields =>
    obtain ⟨args', rfl, HR⟩ := R.const_spine (hctor hi)
    have RP := Lean4Lean.List.forall₂_take HR ps.length
    have RF := Lean4Lean.List.forall₂_drop HR ps.length
    simp only [List.take_left] at RP
    simp only [List.drop_left] at RF
    rw [← List.take_append_drop ps.length args']
    apply ScopedCompare.structFields hi hx (RP.length_eq.symm.trans hp)
      (RF.length_eq.symm.trans hf) hadm
    intro i hj hn
    have hi' : i < fields.length := by rw [RF.length_eq]; exact hj
    have Rfield := RF.getElem_of i hi' hj
    rcases Hfields i hi' with HE | HE
    · rw [HE] at Rfield
      exact (hn (Rfield.proof_fixed hroot)).elim
    · rw [HE] at Rfield
      exact .compute .refl Rfield .refl
end ProofShape

/-- Every finite contextual K-prefix stage preserves a structure-eta guard
after arbitrary computation of its expansion, provided selected delta equations
respect constructor rigidity. Parameters and fields may compute independently. -/
theorem proofErase_scoped_prefix_structure_residual
    (heq : env.HasCanonicalEq) (hD : ConstructorObservation.ConstructorRigid D)
    (H : ProofShape.StructureEtaHead a m)
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ a out) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) Δ true out m := by
  apply R.structure_eta_residual (erased_scoped_prefix_stage_head stage) ?_ H
  intro family info Δ ls args out hi HR
  exact erased_scoped_prefix_stage_no_rigid heq (henv.projectionCtorRigid hi)
    (hD family info hi) stage HR (ProofShape.constHead_mkApps _ _)

/-- A typed original structure expansion retains its comparison with the major
after any finite scoped prefix computation, including whole-proof collapse. -/
theorem proofErase_scoped_prefix_structure_eta_left
    (heq : env.HasCanonicalEq) (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps))
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (structExpand family info ls ps m)) out) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true out
      (proofErase Γ m) := by
  rcases proofErase_structure_eta_forward hΓ hi hp hx hm hexp with E | H
  · rw [E] at R
    exact .compute .refl R .refl
  · exact proofErase_scoped_prefix_structure_residual heq hD H R

/-- The actual stored-definition and registry-selected structure collection
satisfies the required constructor exclusion, with no extra rigidity premise. -/
theorem proofErase_scoped_registered_structure_residual
    (heq : env.HasCanonicalEq) (H : ProofShape.StructureEtaHead a m)
    (R : ProofShape.ScopedCompute
      (ErasedScopedPrefixStage (RegisteredStructure.definitions
        (PureObservation.Definitions.ofEnv env univs henv)) stage) Δ a out) :
    ProofShape.ScopedCompare
      (ErasedScopedPrefixStage (RegisteredStructure.definitions
        (PureObservation.Definitions.ofEnv env univs henv)) stage) Δ true out m :=
  proofErase_scoped_prefix_structure_residual heq
    (RegisteredStructure.definitions_rigid ConstructorObservation.ConstructorRigid.ofEnv) H R

end Lean4Lean.VEnv.Strengthening
