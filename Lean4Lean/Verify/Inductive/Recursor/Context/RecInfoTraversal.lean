import Lean4Lean.Verify.Inductive.Context

/-! Support for the proofs about the executable traversal in `mkRecInfos`: the
proof-side record of the recursive fields selected by `loopCtorArgs`
(`RecursiveFieldDomain`, `RecursiveFieldSelections`), the common-parameter prefix
of a constructor type that `loopCtorArgs` follows (`ParameterPrefix`,
`ParameterSegment`), and small lemmas about the reader monad and array updates
used by the traversal proofs. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursiveFieldDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env decl.uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursiveFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursiveFieldDomain env decl) → Prop
  | nil : RecursiveFieldSelections env decl #[] #[] []
  | nonrecursive : RecursiveFieldSelections env decl bu u fields →
      RecursiveFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursiveFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursiveFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursiveFieldSelections.selectedSublist
    (H : RecursiveFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]



/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[], ruleTemplates := #[] } =
    { b with minors := #[], ruleTemplates := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

end mkRecInfos.loopInd2

end VerifyInductive
end Lean4Lean
