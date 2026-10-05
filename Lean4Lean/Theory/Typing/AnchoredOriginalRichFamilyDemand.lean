import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanLegacy
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyConsumption

/-! A family request under a finite function spine cannot come from a
constructor terminal. This uses the actual query grammar rather than a
literal-shape assumption about the registered raw declaration. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
open private FamilyFunctionDemand.not_sort from Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyConsumption

def FamilyEndDemand : {n : Nat} → Atom n → Prop
  | _+1, .family _ => True
  | _+1, .fn _ output => FamilyEndDemand output
  | _+1, .pad output => FamilyEndDemand output
  | _, _ => False

private theorem FamilyEndDemand.noFamily_function {atom : Atom n}
    (ends : FamilyEndDemand atom)
    (noFamily : FamilyAtomProperty (fun {_} _ => False) atom) : FamilyFunctionDemand atom := by
  induction n with
  | zero => exact ends.elim
  | succ n ih =>
    cases atom with
    | family => exact noFamily.elim
    | fn => trivial
    | pad atom => exact ih ends noFamily
    | sort | pi | ctor | record => exact ends.elim

private theorem familyEnd_of_not_noFamily {atom : Atom n}
    (present : ¬ FamilyAtomProperty (fun {_} _ => False) atom) : FamilyEndDemand atom := by
  induction n with
  | zero => exact (present trivial).elim
  | succ n ih =>
    cases atom with
    | family => trivial
    | pad atom => exact ih present
    | sort | fn | pi | ctor | record => exact (present trivial).elim

theorem FamilyEndDemand.codeBack
    (action : SortableCodeAction env U registry target relevant (.singleton a) next (.singleton b))
    (sorted : (Profile.singleton a).HasType (.sort relevant))
    (ends : FamilyEndDemand b) : FamilyEndDemand a := by
  apply familyEnd_of_not_noFamily
  intro noFamily
  have result := action.familyProperty (property := fun {_} _ => False) (fun impossible => impossible)
    (fun atom member => by cases List.mem_singleton.mp member; exact noFamily) _ (List.mem_singleton_self _)
  exact FamilyFunctionDemand.not_sort (ends.noFamily_function result) (action.preservesSort sorted)

theorem FamilyEndDemand.adapterBack {a b : Atom n}
    (adapter : GeneralAtomAdapter env U registry target a b)
    (ends : FamilyEndDemand b) : FamilyEndDemand a := by
  induction n with
  | zero => exact ends.elim
  | succ n ih =>
    cases adapter with
    | refl => exact ends
    | code action sorted => exact ends.codeBack action sorted
    | fn keys result => exact ih result ends
    | pad child => exact ih child ends

theorem FamilyEndDemand.shift_iff (atom : Atom n) :
    FamilyEndDemand (AdapterNormal.shiftAtom atom) ↔ FamilyEndDemand atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | fn key output => exact ih output
    | sort | pi | family | ctor | record | pad => rfl

theorem FamilyEndDemand.normal_iff (atom : Atom n) :
    FamilyEndDemand (AdapterNormal.atom atom) ↔ FamilyEndDemand atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | fn key output => exact ih output
    | pad output => exact (FamilyEndDemand.shift_iff _).trans (ih output)
    | sort | pi | family | ctor | record => rfl

theorem FamilyEndDemand.normalAdapterBack
    (adapter : GeneralNormalAtomAdapter env U registry target a b)
    (ends : FamilyEndDemand b) : FamilyEndDemand a :=
  (FamilyEndDemand.normal_iff a).mp
    (((FamilyEndDemand.normal_iff b).mpr ends).adapterBack adapter)

theorem FamilyEndDemand.viewBack
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (view : AtomView env U registry target a b)
    (ends : FamilyEndDemand b) : FamilyEndDemand a :=
  ends.normalAdapterBack (view.toGeneralAdapter henv hscoped formed)

theorem FamilyEndDemand.outputBack
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (path : GeneralOutputPath env U registry target a b)
    (ends : FamilyEndDemand b) : FamilyEndDemand a := by
  induction path with
  | refl => exact ends
  | action path action ih => exact ih (ends.normalAdapterBack (action.toGeneralAdapter henv hscoped formed))
  | code path action sorted ih => exact ih (ends.codeBack action sorted)
  | pad path ih | unpad path ih => exact ih ends

/-- A constructor plan cannot hide a family-ending request under its function
binders or output views. -/
theorem RichConstructorPlan.not_familyEnd {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint)
    (member : atom ∈ profile.atoms) (ends : FamilyEndDemand atom) : False := by
  match n, profile, footprint, plan with
  | _, _, _, .terminal .. | _, _, _, .terminalRecord .. => cases List.mem_singleton.mp member; exact ends
  | _, _, _, .binder _ _ _ _ _ _ body _ _ =>
    cases List.mem_singleton.mp member
    exact RichConstructorPlan.not_familyEnd henv hscoped formed body (List.mem_singleton_self _) ends
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    exact RichConstructorPlan.not_familyEnd henv hscoped formed source (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
  | _, _, _, .pad source =>
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact RichConstructorPlan.not_familyEnd henv hscoped formed source present ends
termination_by sizeOf plan

theorem ConstructorPlan.not_familyEnd {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (plan : ConstructorPlan env U registry target name levels signature arguments profile footprint)
    (member : atom ∈ profile.atoms) (ends : FamilyEndDemand atom) : False := by
  match n, profile, footprint, plan with
  | _, _, _, .terminal .. => cases List.mem_singleton.mp member; exact ends
  | _, _, _, .binder _ _ _ body _ _ =>
    cases List.mem_singleton.mp member
    exact ConstructorPlan.not_familyEnd henv hscoped formed body (List.mem_singleton_self _) ends
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    exact ConstructorPlan.not_familyEnd henv hscoped formed source (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
  | _, _, _, .pad source =>
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ConstructorPlan.not_familyEnd henv hscoped formed source present ends
termination_by sizeOf plan

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
