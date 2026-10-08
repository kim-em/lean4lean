import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Verify.Inductive.Nested.Replacement
import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Ordered flattened restored-primary equation trace.  The left list is the
independent source declaration's owner/constructor traversal, so this
relation fixes both order and cardinality rather than accepting a separate
indexing callback. -/
abbrev RestoredPrimaryIotaListTrace
    (decl : VInductDecl) (block : VInductBlock)
    (owned : List (VInductiveType × VConstVal))
    (rules : List VDefEq) : Prop :=
  List.Forall₂ (fun ownerCtor rule =>
    Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
    owned rules

/-- An exact trace over `ownedConstructors` is precisely the ordered
`NestedIotaListCertificate` consumed by nested compilation. -/
theorem NestedIotaListCertificate.ofForall₂
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : RestoredPrimaryIotaListTrace decl block
      decl.ownedConstructors rules) :
    NestedIotaListCertificate decl block rules where
  length :=
    (Lean4Lean.List.Forall₂.length_eq H).symm
  rules i hctor hrule :=
    Lean4Lean.List.forall₂_getElem H i hctor hrule

end VerifyInductive
end Lean4Lean
