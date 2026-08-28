import Lean4Lean.Verify.Inductive.Nested.EquationRestorationList

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Owner-indexed constructor order used while restored primary equations are
assembled one family at a time. -/
def ownedConstructorsFor (owners : List VInductiveType) :
    List (VInductiveType × VConstVal) :=
  owners.flatMap fun owner => owner.ctors.map (owner, ·)

theorem ownedConstructorsFor_eq
    (decl : VInductDecl) :
    ownedConstructorsFor decl.types = decl.ownedConstructors :=
  rfl

/-- Exact family-by-family restored-primary equation batch.  Each head batch
is indexed by the constructors of the corresponding source owner, and the
result list is definitionally the concatenation in mutual-family order. -/
inductive RestoredPrimaryIotaFamilyTrace
    (decl : VInductDecl) (block : VInductBlock) :
    List VInductiveType → List VDefEq → Prop
  | nil : RestoredPrimaryIotaFamilyTrace decl block [] []
  | cons {owner owners head tail}
      (Hhead : List.Forall₂ (fun ownerCtor rule =>
        Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
        (owner.ctors.map (owner, ·)) head)
      (Htail : RestoredPrimaryIotaFamilyTrace decl block owners tail) :
      RestoredPrimaryIotaFamilyTrace decl block (owner :: owners)
        (head ++ tail)

/-- Family-local batches flatten to the single ordered trace consumed by the
independent nested-iota specification. -/
theorem RestoredPrimaryIotaFamilyTrace.forall₂
    (H : RestoredPrimaryIotaFamilyTrace decl block owners rules) :
    RestoredPrimaryIotaListTrace decl block
      (ownedConstructorsFor owners) rules := by
  induction H with
  | nil => exact .nil
  | @cons owner owners head tail Hhead Htail ih =>
    simpa [ownedConstructorsFor] using
      Lean4Lean.VerifyInductive.List.Forall₂.append' Hhead ih

/-- Once source restoration has fixed the declaration's owner list, the
family-local batches give the complete ordered primary iota certificate.
Mutual flattening, coverage, and cardinality are therefore not separate
callbacks at compilation assembly. -/
theorem RestoredPrimaryIotaFamilyTrace.certificate
    (Hrules : RestoredPrimaryIotaFamilyTrace decl block owners rules)
    (htypes : decl.types = owners)
    :
    NestedIotaListCertificate decl block rules := by
  apply NestedIotaListCertificate.ofForall₂
  rw [← ownedConstructorsFor_eq decl, htypes]
  exact Hrules.forall₂

end VerifyInductive
end Lean4Lean
