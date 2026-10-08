import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! This module deliberately sits below recursor installation. -/

inductive ConstructorValidationSteps (P : α → σ → σ → Type) :
    List α → σ → σ → Type
  | nil : ConstructorValidationSteps P [] source source
  | cons : P head source middle →
      ConstructorValidationSteps P tail middle target →
      ConstructorValidationSteps P (head :: tail) source target

private theorem constructorValidationForM_refines
    (step : α → StateT σ (Except Exception) Unit)
    (P : α → σ → σ → Type) :
    ∀ (items : List α),
      (∀ item, item ∈ items → ∀ source,
        (step item source).WF fun out =>
          out.1 = () ∧ Nonempty (P item source out.2)) →
      ∀ source,
      (items.forM step source).WF fun out =>
        out.1 = () ∧ Nonempty
          (ConstructorValidationSteps P items source out.2) := by
  intro items
  induction items with
  | nil =>
    intro _ source
    exact Except.WF.pure ⟨rfl, ⟨.nil⟩⟩
  | cons head tail ih =>
    intro Hstep source
    rw [List.forM]
    exact (Hstep head (by simp) source).bind fun out Hout => by
      rcases out with ⟨unit, middle⟩
      rcases unit with ⟨⟩
      rcases Hout with ⟨_, ⟨Hhead⟩⟩
      have Htail := ih (fun item hitem =>
        Hstep item (by simp [hitem])) middle
      exact Htail.mono fun out Hout => by
        rcases out with ⟨unit, target⟩
        rcases unit with ⟨⟩
        rcases Hout with ⟨_, ⟨Hrest⟩⟩
        exact ⟨rfl, ⟨.cons Hhead Hrest⟩⟩

structure ValidationHeaderStep
    (loweredEnv : Environment) (allIndNames : List Name)
    (indName : Name) (sourceEnv targetEnv : Environment) where
  oldInfo : InductiveVal
  lookup : loweredEnv.find? indName = some (.inductInfo oldInfo)
  fresh : sourceEnv.contains oldInfo.name = false
  output : targetEnv = sourceEnv.add
    (.inductInfo { oldInfo with all := allIndNames })

private theorem restoreInductiveHeaderDecl_validationWF
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indName : Name) :
    (Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indName sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ValidationHeaderStep loweredEnv
          allIndNames indName sourceEnv out.2) := by
  intro out hout
  unfold Lean4Lean.restoreInductiveHeaderDecl at hout
  split at hout
  next oldInfo hlookup =>
    change (sourceEnv.checkName oldInfo.name allowPrimitive).map (fun _ =>
      ((), sourceEnv.add (.inductInfo
        { oldInfo with all := allIndNames }))) = .ok out at hout
    cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
    | error err => simp [Except.map, hcheck] at hout
    | ok checked =>
      simp only [Except.map, hcheck, Except.ok.injEq] at hout
      subst out
      have hfresh : sourceEnv.contains oldInfo.name = false := by
        cases hcontains : sourceEnv.contains oldInfo.name
        · rfl
        · have himpossible :
            (Except.error (.alreadyDeclared sourceEnv oldInfo.name) :
                Except Exception Unit) = .ok checked := by
            simpa [Lean.Kernel.Environment.checkName, hcontains, bind,
              Except.bind] using hcheck
          cases himpossible
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        fresh := hfresh
        output := rfl }⟩⟩
  next other hlookup => simp at hout

structure ValidationConstructorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool) (ctorName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : ConstructorVal
  lookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo)
  fresh : sourceEnv.contains oldInfo.name = false
  notPrimitive : allowPrimitive = false →
    Kernel.Environment.primitives.contains oldInfo.name = false
  output : targetEnv = sourceEnv.add (.ctorInfo { oldInfo with
    type := result.restoreNested loweredEnv oldInfo.type })

private theorem restoreConstructorDecl_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorName : Name) :
    (Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
      ctorName sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ValidationConstructorStep result
          loweredEnv allowPrimitive ctorName sourceEnv out.2) := by
  intro out hout
  unfold Lean4Lean.restoreConstructorDecl at hout
  split at hout
  next oldInfo hlookup =>
    change (sourceEnv.checkName oldInfo.name allowPrimitive).map (fun _ =>
      ((), sourceEnv.add (.ctorInfo { oldInfo with
        type := result.restoreNested loweredEnv oldInfo.type }))) =
          .ok out at hout
    cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
    | error err => simp [Except.map, hcheck] at hout
    | ok checked =>
      simp only [Except.map, hcheck, Except.ok.injEq] at hout
      subst out
      have hfresh : sourceEnv.contains oldInfo.name = false := by
        cases hcontains : sourceEnv.contains oldInfo.name
        · rfl
        · have himpossible :
            (Except.error (.alreadyDeclared sourceEnv oldInfo.name) :
                Except Exception Unit) = .ok checked := by
            simpa [Lean.Kernel.Environment.checkName, hcontains, bind,
              Except.bind] using hcheck
          cases himpossible
      have hnprim : allowPrimitive = false →
          Kernel.Environment.primitives.contains oldInfo.name = false := by
        intro hallow
        cases hprimitive : Kernel.Environment.primitives.contains oldInfo.name
        · rfl
        · simp [Lean.Kernel.Environment.checkName, hfresh, hallow,
            hprimitive, bind, Except.bind] at hcheck
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        fresh := hfresh
        notPrimitive := hnprim
        output := rfl }⟩⟩
  next other hlookup => simp at hout

structure ValidationFamilyStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool)
    (indType : InductiveType)
    (sourceEnv targetEnv : Environment) where
  oldInfo : InductiveVal
  lookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)
  constructors : ConstructorValidationSteps
    (ValidationConstructorStep result loweredEnv allowPrimitive)
    oldInfo.ctors sourceEnv targetEnv

private theorem restoreInductiveConstructorsOnly_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (indType : InductiveType) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreInductiveConstructorsOnly result loweredEnv
      allowPrimitive indType sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty
          (ValidationFamilyStep result loweredEnv
            allowPrimitive indType sourceEnv out.2) := by
  unfold Lean4Lean.restoreInductiveConstructorsOnly
  simp only [hlookup]
  have Hconstructors := constructorValidationForM_refines
    (fun ctorName => Lean4Lean.restoreConstructorDecl result loweredEnv
      allowPrimitive ctorName)
    (ValidationConstructorStep result loweredEnv allowPrimitive)
    oldInfo.ctors
    (fun ctorName _ currentEnv =>
      restoreConstructorDecl_validationWF result loweredEnv currentEnv
        allowPrimitive ctorName)
    sourceEnv
  exact Hconstructors.mono fun out Hout => by
    rcases out with ⟨unit, targetEnv⟩
    rcases unit with ⟨⟩
    rcases Hout with ⟨_, ⟨Hconstructors⟩⟩
    exact ⟨trivial, ⟨{
      oldInfo := oldInfo
      lookup := hlookup
      constructors := Hconstructors }⟩⟩

structure ValidationEnvironment
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType)
    (targetEnv : Environment) where
  headerEnv : Environment
  headers : ConstructorValidationSteps
    (fun indType source target => ValidationHeaderStep loweredEnv
      allIndNames indType.name source target)
    types sourceEnv headerEnv
  constructors : ConstructorValidationSteps
    (ValidationFamilyStep result loweredEnv
      allowPrimitive)
    types headerEnv targetEnv

/-- Exact side environment obtained by restoring just the mutually recursive
source headers.  This is the executable dependency boundary for validating
cached nested-family applications. -/
structure ValidationHeaderEnvironment
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (types : List InductiveType) (targetEnv : Environment) where
  headers : ConstructorValidationSteps
    (fun indType source target => ValidationHeaderStep loweredEnv
      allIndNames indType.name source target)
    types sourceEnv targetEnv

theorem restoreNestedHeaders_validationWF
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType) :
    (Lean4Lean.restoreNestedHeaders loweredEnv allIndNames allowPrimitive
      types sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ValidationHeaderEnvironment
          loweredEnv sourceEnv allIndNames types out.2) := by
  unfold Lean4Lean.restoreNestedHeaders
  have Hheaders := constructorValidationForM_refines
    (fun indType => Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indType.name)
    (fun indType source target => ValidationHeaderStep loweredEnv
      allIndNames indType.name source target)
    types
    (fun indType _ currentEnv =>
      restoreInductiveHeaderDecl_validationWF loweredEnv currentEnv
        allIndNames allowPrimitive indType.name)
    sourceEnv
  exact Hheaders.mono fun out Hout => by
    rcases out with ⟨unit, targetEnv⟩
    rcases unit with ⟨⟩
    rcases Hout with ⟨_, ⟨Htrace⟩⟩
    exact ⟨rfl, ⟨⟨Htrace⟩⟩⟩

theorem restoreNestedConstructors_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreNestedConstructors result loweredEnv allIndNames
      allowPrimitive types sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ValidationEnvironment result
          loweredEnv sourceEnv allIndNames allowPrimitive types out.2) := by
  unfold Lean4Lean.restoreNestedConstructors
  have Hheaders := restoreNestedHeaders_validationWF loweredEnv sourceEnv
    allIndNames allowPrimitive types
  exact Hheaders.bind fun out Hout => by
    rcases out with ⟨unit, headerEnv⟩
    rcases unit with ⟨⟩
    rcases Hout with ⟨_, ⟨HheaderEnvironment⟩⟩
    let Hheaders := HheaderEnvironment.headers
    have Hconstructors := constructorValidationForM_refines
      (fun indType => Lean4Lean.restoreInductiveConstructorsOnly result
        loweredEnv allowPrimitive indType)
      (ValidationFamilyStep result loweredEnv
        allowPrimitive)
      types
      (fun indType hind currentEnv => by
        rcases Htypes indType hind with ⟨oldInfo, hlookup⟩
        exact restoreInductiveConstructorsOnly_validationWF result loweredEnv
          currentEnv allowPrimitive indType oldInfo hlookup)
      headerEnv
    exact Hconstructors.mono fun out Hout => by
      rcases out with ⟨unit, targetEnv⟩
      rcases unit with ⟨⟩
      rcases Hout with ⟨_, ⟨Hconstructors⟩⟩
      exact ⟨rfl, ⟨{
        headerEnv := headerEnv
        headers := Hheaders
        constructors := Hconstructors }⟩⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem AddConstants.valueNonprimitive
    (H : AddConstants safety prodEnv venv entries outProdEnv outVEnv)
    (hvalue : value ∈ entries.map Prod.snd) :
    ¬ Kernel.Environment.primitives.contains value.name := by
  induction H with
  | nil => simp at hvalue
  | cons hn hnprim htr hwf hadd hdelta Htail ih =>
    simp only [List.map_cons, List.mem_cons] at hvalue
    rcases hvalue with hhead | htail
    · subst value
      simpa [htr.2] using hnprim
    · exact ih htail

end VerifyInductive
end Lean4Lean
