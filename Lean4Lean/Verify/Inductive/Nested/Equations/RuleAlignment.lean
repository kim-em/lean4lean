import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.SignatureVars
import Lean4Lean.Theory.Typing.RestorationShapes

/-! # Heads of the compilation restoration

Every head of `compilationRestoration source auxiliaries` has the source parameter count, and
no generated recursor name is one of its heads. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace InductiveSignature

theorem compilationRestoration_heads_nparams {source : VInductDecl}
    {auxiliaries : List ContainerSpecialization} :
    ∀ h ∈ (compilationRestoration source auxiliaries).heads, h.nparams = source.nparams := by
  intro h hh
  simp only [compilationRestoration, List.mem_flatMap, ContainerSpecialization.heads,
    List.mem_cons, List.mem_map] at hh
  obtain ⟨a, -, rfl | ⟨ctor, -, rfl⟩⟩ := hh <;> rfl

/-- A generated recursor name is not a restoration head: the heads are the auxiliary families
and their constructors, names of the expanded declaration, from which the generated recursor
names are distinct (`CompilationData.generatedNames`). -/
theorem CompilationData.recursorName_not_head {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block) (owner : Fin s.families.size) :
    (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == g.recursorName owner) = none := by
  apply Restoration.heads_find?_eq_none
  intro hmem
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  rw [compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect] at hmem
  have hnames := RestoresFamily.familyNames hfamilies
  have hnd : (expanded.sourceNames ++ g.recursors.map (·.name)).Nodup := by
    simpa only [VInductDecl.sourceNames, List.map_append, List.append_assoc] using
      H.generatedNames
  have he : g.recursorName owner ∈ familyNames expanded.types := by
    rw [← H.model.familyNames, hnames]
    simpa only [familyNames, List.flatMap_append] using
      List.mem_append_right (familyNames source.types) hmem
  have he' : g.recursorName owner ∈ expanded.sourceNames := by
    have := (familyNames_perm expanded.types).mem_iff.mp he
    simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
      using this
  have hr : g.recursorName owner ∈ g.recursors.map (·.name) :=
    List.mem_map.2 ⟨g.recursor owner,
      List.mem_map.2 ⟨owner, List.mem_finRange _, rfl⟩, rfl⟩
  exact (List.nodup_append.mp hnd).2.2 _ he' _ hr rfl

end InductiveSignature

namespace VExpr

end VExpr

open InductiveSignature

namespace VerifyInductive
namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

end RestoredBlock
end VerifyInductive
end Lean4Lean
