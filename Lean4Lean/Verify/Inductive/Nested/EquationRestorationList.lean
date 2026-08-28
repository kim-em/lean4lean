import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIotaStructural

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
    (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H).symm
  rules i hctor hrule :=
    Lean4Lean.VerifyInductive.List.Forall₂.getElem H i hctor hrule

/-- Pointwise restored-primary rules can be accumulated without losing their
source owner/constructor index. -/
theorem RestoredPrimaryIotaListTrace.prepend
    {decl : VInductDecl} {block : VInductBlock}
    {owned : VInductiveType × VConstVal} {rule : VDefEq}
    {owneds : List (VInductiveType × VConstVal)} {rules : List VDefEq}
    (Hhead : Nonempty (decl.NestedIotaRule block owned.1 owned.2 rule))
    (Htail : RestoredPrimaryIotaListTrace decl block owneds rules) :
    RestoredPrimaryIotaListTrace decl block (owned :: owneds)
      (rule :: rules) :=
  List.Forall₂.cons Hhead Htail

end VerifyInductive
end Lean4Lean
