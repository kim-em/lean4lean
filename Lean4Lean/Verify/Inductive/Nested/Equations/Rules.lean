import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Equations.RuleAlignment
import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.RestorationHead

/-! # The typing of the restored block

The projection stage and the recursor stage of the restored block are well formed, and the
restored block is well formed (`RestoredBlock.blockWF`): its equations are typed in the
restored recursor stage (`RestoredBlock.restoredEquationsWF`, by transport of the lowered
run's equations along the restoration interpretation,
`Theory/Inductive/RestorationInterpretation.lean`). With it the restored declaration satisfies
`VInductDecl.WF` (`RestoredBlock.wf'`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The projection stage of the restored block is well formed. -/
theorem envP_wf (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.envP.WF :=
  TrInductDeclCore.projectionStageWF B.source Hc.wf (.nested B.formation .rfl)

/-- The restored recursor stage is well formed. -/
theorem envR_wf (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.envR.WF := by
  have h := B.recsAdded
  rw [VInductDecl.addRecs_eq_addConstVals] at h
  refine VEnv.WF.addConstVals B.envP_wf ?_ h
  intro ci hci
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci
  exact B.recs_wf r hr

-- `restoredEquationsWF` is a field of `RestoredBlock`, produced in `nestedRestoredBlock` from
-- `NestedRun.hrestoredWF_of` (`Nested/Restoration/Equations/RestoredWF.lean`).

/-- The restored block is well formed: its equations are typed in the restored recursor
stage. -/
theorem blockWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.block.WF Hc.venv := by
  have htypes : B.block.types = B.decl.typeConstants := B.compiled.types
  have hctors : B.block.ctors = B.decl.constructorConstants := B.compiled.ctors
  have hprojs : B.block.projections = B.decl.projectionEntries := B.compiled.projections
  have hrecs : B.block.recursors = B.decl.recs.map (·.toVConstVal) := B.recsOf.recursors.symm
  refine ⟨B.envTypes, B.envCtors, B.envR, htypes ▸ B.source.typesAdded,
    hctors ▸ B.source.ctorsAdded, ?_, ?_, ?_, ?_, B.restoredEquationsWF⟩
  · have h := B.recsAdded
    rw [VInductDecl.addRecs_eq_addConstVals] at h
    rw [hprojs, hrecs]; exact h
  · intro ci hci
    rw [htypes] at hci
    simp only [VInductDecl.typeConstants, List.mem_map] at hci
    obtain ⟨t, ht, rfl⟩ := hci
    exact TrInductDeclCore.typeHeadersWF B.source t ht
  · intro ci hci
    rw [hctors] at hci
    simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
    obtain ⟨t, ht, hci⟩ := hci
    obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r B.source.types t ht
    obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
    exact Hc.wf
  · rw [hrecs, hprojs]
    intro ci hci
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci
    exact B.recs_wf r hr

/-- `VInductDecl.WF` of the restored declaration. -/
theorem wf' (B : RestoredBlock L sourceTypes isUnsafe outEnv) (hsource : sourceTypes ≠ []) :
    B.decl.WF Hc.venv :=
  B.wf hsource B.blockWF

/-- The compiled block with its typing, for `BlockCertificate.compiled`. -/
theorem compiledWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∃ block, B.decl.CompilesTo Hc.venv block ∧ B.decl.RecsOf block ∧ block.WF Hc.venv :=
  ⟨B.block, B.compilesTo, B.recsOf, B.blockWF⟩

end RestoredBlock
end VerifyInductive
end Lean4Lean
