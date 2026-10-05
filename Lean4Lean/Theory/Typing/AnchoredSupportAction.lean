import Lean4Lean.Theory.Typing.AnchoredFlatSorts
import Lean4Lean.Theory.Typing.AnchoredViewTyping

/-! Finite computed actions on assigned type supports. Output actions retain
all old Pi rows and add transformed rows at the same frozen key. There is no
semantic producer in this syntax. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

inductive SupportAction (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (context : List VExpr) : Nat → Type where
  | id : SupportAction env U registry context n
  | flatSorts : SupportAction env U registry context n
  | view {a b : Atom n} (view : AtomView env U registry context a b) :
      SupportAction env U registry context n
  | output (key : Key n) (child : SupportAction env U registry context n) :
      SupportAction env U registry context (n + 1)
  | pad (child : SupportAction env U registry context n) :
      SupportAction env U registry context (n + 1)
  | comp (first second : SupportAction env U registry context n) :
      SupportAction env U registry context n
  | union (first second : SupportAction env U registry context n) :
      SupportAction env U registry context n

noncomputable def SupportAction.apply (action : SupportAction env U registry context n)
    (profile : Profile n) : Profile n :=
  match action with
  | .id => profile
  | .flatSorts => profile.flatSorts
  | .view v => v.mapType profile
  | .output key child => outputTypes key child.apply profile
  | .pad child => (child.apply profile.down).pad
  | .comp first second => second.apply (first.apply profile)
  | .union first second => (first.apply profile).union (second.apply profile)

open private outputTypes_wf outputTypes_sort from
  Lean4Lean.Theory.Typing.AnchoredViewTyping

theorem SupportAction.wf (action : SupportAction env U registry context n)
    (formed : profile.WF) : (action.apply profile).WF := by
  induction action with
  | id => exact formed
  | flatSorts => exact formed.flatSorts
  | view view => exact view.mapType_wf formed
  | output key child ih => exact outputTypes_wf (fun _ h => ih h) formed
  | pad child ih => exact (ih formed.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH formed)
  | union first second firstIH secondIH => exact (firstIH formed).union (secondIH formed)

theorem SupportAction.preservesSort (action : SupportAction env U registry context n)
    (formed : profile.HasType (.sort relevant)) :
    (action.apply profile).HasType (.sort relevant) := by
  induction action generalizing relevant with
  | id => exact formed
  | flatSorts => exact formed.flatSorts_sort
  | view view => exact view.mapType_sort formed
  | output key child ih =>
    exact outputTypes_sort (fun _ h => child.wf h) (fun _ _ h => ih h) formed
  | pad child ih =>
    exact (ih (by simpa only [Profile.down_sort] using formed.down)).pad_sort
  | comp first second firstIH secondIH => exact secondIH (firstIH formed)
  | union first second firstIH secondIH => exact (firstIH formed).union (secondIH formed)

noncomputable def SupportAction.mixed {source target : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (insertion : MixedInsertion env U source target ρ)
    (action : SupportAction env U registry source n) :
    SupportAction env U registry target n :=
  match action with
  | .id => .id
  | .flatSorts => .flatSorts
  | .view v => .view (v.mixed henv insertion)
  | .output key child => .output (key.rename ρ) (child.mixed henv insertion)
  | .pad child => .pad (child.mixed henv insertion)
  | .comp first second => .comp (first.mixed henv insertion) (second.mixed henv insertion)
  | .union first second => .union (first.mixed henv insertion) (second.mixed henv insertion)

noncomputable def SupportAction.future {source target : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (insertion : FutureInsertion env U source target ρ)
    (action : SupportAction env U registry source n) :
    SupportAction env U registry target n :=
  match action with
  | .id => .id
  | .flatSorts => .flatSorts
  | .view v => .view (v.future henv insertion)
  | .output key child => .output (key.rename ρ) (child.future henv insertion)
  | .pad child => .pad (child.future henv insertion)
  | .comp first second => .comp (first.future henv insertion) (second.future henv insertion)
  | .union first second => .union (first.future henv insertion) (second.future henv insertion)

theorem SupportAction.apply_mixed {source target : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (insertion : MixedInsertion env U source target ρ)
    (action : SupportAction env U registry source n) (profile : Profile n) :
    (action.apply profile).rename ρ = (action.mixed henv insertion).apply (profile.rename ρ) := by
  induction action with
  | id => rfl
  | flatSorts => exact (Profile.flatSorts_rename profile ρ).symm
  | view view => exact view.mapType_mixed henv insertion profile
  | output key child ih => exact outputTypes_rename key _ _ ih profile
  | pad child ih =>
    simpa only [apply, mixed, Profile.rename_pad, Profile.down_rename] using
      congrArg Profile.pad (ih profile.down)
  | comp first second firstIH secondIH =>
    exact (secondIH (first.apply profile)).trans (congrArg _ (firstIH profile))
  | union first second firstIH secondIH =>
    simp only [apply, mixed, Profile.rename_union, firstIH, secondIH]

theorem SupportAction.apply_future {source target : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (insertion : FutureInsertion env U source target ρ)
    (action : SupportAction env U registry source n) (profile : Profile n) :
    (action.apply profile).rename ρ = (action.future henv insertion).apply (profile.rename ρ) := by
  induction action with
  | id => rfl
  | flatSorts => exact (Profile.flatSorts_rename profile ρ).symm
  | view view => exact view.mapType_future henv insertion profile
  | output key child ih => exact outputTypes_rename key _ _ ih profile
  | pad child ih =>
    simpa only [apply, future, Profile.rename_pad, Profile.down_rename] using
      congrArg Profile.pad (ih profile.down)
  | comp first second firstIH secondIH =>
    exact (secondIH (first.apply profile)).trans (congrArg _ (firstIH profile))
  | union first second firstIH secondIH =>
    simp only [apply, future, Profile.rename_union, firstIH, secondIH]

end Lean4Lean.AnchoredSemantics
