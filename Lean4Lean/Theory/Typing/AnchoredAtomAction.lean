import Lean4Lean.Theory.Typing.AnchoredSupportActionInterpretation
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionInterpretation

/-! Finite actions on one requested value atom. Code actions are admitted
only with the actual intrinsic sort classification; lifting through function
outputs computes a finite action on their covering Pi rows. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

inductive AtomAction (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (context : List VExpr) : {n : Nat} → Atom n → Atom n → Type where
  | view (view : AtomView env U registry context a b) : AtomAction env U registry context a b
  | code (action : SortableCodeAction env U registry context relevant
        (Profile.singleton a) next (Profile.singleton b))
      (formed : (Profile.singleton a).HasType (.sort relevant)) :
      AtomAction env U registry context a b
  | fn (key : Key n) (child : AtomAction env U registry context a b) :
      AtomAction env U registry context (n := n + 1) (.fn key a) (.fn key b)
  | pad {a b : Atom n} (child : AtomAction env U registry context a b) :
      AtomAction env U registry context (n := n + 1) (.pad a) (.pad b)
  | comp (first : AtomAction env U registry context a b)
      (second : AtomAction env U registry context b c) : AtomAction env U registry context a c

noncomputable def AtomAction.support {a b : Atom n} (action : AtomAction env U registry context a b) :
    SupportAction env U registry context n :=
  match n, a, b, action with
  | _, _, _, .view v => .view v
  | _, _, _, .code .. => .flatSorts
  | _ + 1, _, _, .fn key child => .output key child.support
  | _ + 1, _, _, .pad child => .pad child.support
  | _, _, _, .comp first second => .comp first.support second.support

open private outputTypes_typed from Lean4Lean.Theory.Typing.AnchoredViewTyping

theorem AtomAction.typed {a b : Atom n} (action : AtomAction env U registry context a b)
    (typed : (Profile.singleton a).HasType profile) :
    (Profile.singleton b).HasType (action.support.apply profile) := by
  induction action with
  | view v => exact v.mapType_typed typed
  | code action formed => exact action.typedAtSorts (formed.flatSorts typed)
  | fn key child ih => exact outputTypes_typed (fun _ h => child.support.wf h) (fun _ h => ih h) typed
  | pad child ih =>
    change (Profile.singleton _).pad.HasType _ at typed
    exact (ih typed.pad_inv).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH typed)

noncomputable def AtomAction.mixed {source target : List VExpr} {ρ : Lift}
    {a b : Atom n} (henv : env.Ordered) (insertion : MixedInsertion env U source target ρ)
    (action : AtomAction env U registry source a b) :
    AtomAction env U registry target (a.rename ρ) (b.rename ρ) :=
  match n, a, b, action with
  | _, _, _, .view v => .view (v.mixed henv insertion)
  | _, _, _, .code leaf formed => .code (by simpa only [Profile.rename_singleton] using leaf.mixed henv insertion)
      (by simpa only [Profile.rename_singleton, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed)
  | _ + 1, _, _, .fn key child => .fn (key.rename ρ) (child.mixed henv insertion)
  | _ + 1, _, _, .pad child => .pad (child.mixed henv insertion)
  | _, _, _, .comp first second => .comp (first.mixed henv insertion) (second.mixed henv insertion)

noncomputable def AtomAction.future {source target : List VExpr} {ρ : Lift}
    {a b : Atom n} (henv : env.Ordered) (insertion : FutureInsertion env U source target ρ)
    (action : AtomAction env U registry source a b) :
    AtomAction env U registry target (a.rename ρ) (b.rename ρ) :=
  match n, a, b, action with
  | _, _, _, .view v => .view (v.future henv insertion)
  | _, _, _, .code leaf formed => .code (by simpa only [Profile.rename_singleton] using leaf.future henv insertion)
      (by simpa only [Profile.rename_singleton, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed)
  | _ + 1, _, _, .fn key child => .fn (key.rename ρ) (child.future henv insertion)
  | _ + 1, _, _, .pad child => .pad (child.future henv insertion)
  | _, _, _, .comp first second => .comp (first.future henv insertion) (second.future henv insertion)

theorem AtomAction.support_mixed {source target : List VExpr} {ρ : Lift}
    {a b : Atom n} (henv : env.Ordered) (insertion : MixedInsertion env U source target ρ)
    (action : AtomAction env U registry source a b) :
    (action.mixed henv insertion).support = action.support.mixed henv insertion := by
  induction action with
  | view | code => rfl
  | fn key child ih => exact congrArg (SupportAction.output (key.rename ρ)) ih
  | pad child ih => exact congrArg SupportAction.pad ih
  | comp first second firstIH secondIH => simp only [mixed, support, SupportAction.mixed, firstIH, secondIH]

theorem AtomAction.support_future {source target : List VExpr} {ρ : Lift}
    {a b : Atom n} (henv : env.Ordered) (insertion : FutureInsertion env U source target ρ)
    (action : AtomAction env U registry source a b) :
    (action.future henv insertion).support = action.support.future henv insertion := by
  induction action with
  | view | code => rfl
  | fn key child ih => exact congrArg (SupportAction.output (key.rename ρ)) ih
  | pad child ih => exact congrArg SupportAction.pad ih
  | comp first second firstIH secondIH => simp only [future, support, SupportAction.future, firstIH, secondIH]

end Lean4Lean.AnchoredSemantics
