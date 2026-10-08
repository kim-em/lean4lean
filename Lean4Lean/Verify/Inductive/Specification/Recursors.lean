import Lean4Lean.Verify.Inductive.Specification.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Append-oriented invariant matching the recursor-generation loop. -/
structure RecursorBuildCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  covered : recursors.length ≤ decl.types.length
  shapes : ∀ i (hrec : i < recursors.length)
      (htype : i < decl.types.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

theorem RecursorBuildCertificate.empty (decl : VInductDecl) :
    RecursorBuildCertificate decl [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

/-- Complete restored-primary equation list for a nested declaration.  Its
pointwise judgment permits the auxiliary motive/minor telescope retained by
the exact restored recursor shape and fields consumed by auxiliary recursors. -/
structure NestedIotaListCertificate (decl : VInductDecl)
    (block : VInductBlock) (ruleList : List VDefEq) : Prop where
  length : ruleList.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < ruleList.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 ruleList[i])

/-- Append-oriented form used while source primary batches are selected from
the expanded generated-rule traversal. -/
structure NestedIotaBuildCertificate (decl : VInductDecl)
    (block : VInductBlock) (rules : List VDefEq) : Prop where
  covered : rules.length ≤ decl.ownedConstructors.length
  shapes : ∀ i (hrule : i < rules.length)
      (hctor : i < decl.ownedConstructors.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 rules[i])

theorem NestedIotaBuildCertificate.empty
    (decl : VInductDecl) (block : VInductBlock) :
    NestedIotaBuildCertificate decl block [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

/-- Ordinary compilation of a staged block: its layout and name uniqueness,
the direct canonical generation witness (read by the `Eq` bootstrap), and the
shared finite derivation. -/
structure OrdinaryCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))
  canonical : InductiveSignature.Compiles env decl block
  finite : CompiledInductive env decl block

theorem OrdinaryCompilationCertificate.compilesTo
    (H : OrdinaryCompilationCertificate env decl block) : decl.CompilesTo env block :=
  ⟨H.types, H.ctors, H.projections, H.names, H.finite⟩


end VerifyInductive
end Lean4Lean
