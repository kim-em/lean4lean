import Lean4Lean.Verify.Inductive.Context

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! This module deliberately sits below recursor installation. -/

inductive ConstructorValidationStateTrace (P : α → σ → σ → Type) :
    List α → σ → σ → Type
  | nil : ConstructorValidationStateTrace P [] source source
  | cons : P head source middle →
      ConstructorValidationStateTrace P tail middle target →
      ConstructorValidationStateTrace P (head :: tail) source target

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
          (ConstructorValidationStateTrace P items source out.2) := by
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

structure ConstructorValidationHeaderStep
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
        out.1 = () ∧ Nonempty (ConstructorValidationHeaderStep loweredEnv
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

structure ConstructorValidationConstructorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (ctorName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : ConstructorVal
  lookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo)
  fresh : sourceEnv.contains oldInfo.name = false
  output : targetEnv = sourceEnv.add (.ctorInfo { oldInfo with
    type := result.restoreNested loweredEnv oldInfo.type })

private theorem restoreConstructorDecl_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorName : Name) :
    (Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
      ctorName sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ConstructorValidationConstructorStep result
          loweredEnv ctorName sourceEnv out.2) := by
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
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        fresh := hfresh
        output := rfl }⟩⟩
  next other hlookup => simp at hout

structure ConstructorValidationFamilyStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (allIndNames : List Name)
    (indType : InductiveType) (sourceEnv targetEnv : Environment) where
  headerEnv : Environment
  header : ConstructorValidationHeaderStep loweredEnv allIndNames indType.name
    sourceEnv headerEnv
  constructors : ConstructorValidationStateTrace
    (ConstructorValidationConstructorStep result loweredEnv)
    header.oldInfo.ctors headerEnv targetEnv

private theorem restoreInductiveConstructors_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indType : InductiveType)
    (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreInductiveConstructors result loweredEnv allIndNames
      allowPrimitive indType sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (ConstructorValidationFamilyStep result
          loweredEnv allIndNames indType sourceEnv out.2) := by
  unfold Lean4Lean.restoreInductiveConstructors
  simp only [hlookup]
  exact (restoreInductiveHeaderDecl_validationWF loweredEnv sourceEnv
    allIndNames allowPrimitive indType.name).bind fun out Hout => by
        rcases out with ⟨unit, headerEnv⟩
        rcases unit with ⟨⟩
        rcases Hout with ⟨_, ⟨Hheader⟩⟩
        have holdInfo : Hheader.oldInfo = oldInfo := by
          have hci := Option.some.inj (Hheader.lookup.symm.trans hlookup)
          exact ConstantInfo.inductInfo.inj hci
        cases holdInfo
        have Hctors := constructorValidationForM_refines
          (fun ctorName => Lean4Lean.restoreConstructorDecl result loweredEnv
            allowPrimitive ctorName)
          (ConstructorValidationConstructorStep result loweredEnv)
          Hheader.oldInfo.ctors
          (fun ctorName _ currentEnv =>
            restoreConstructorDecl_validationWF result loweredEnv currentEnv
              allowPrimitive ctorName)
          headerEnv
        exact Hctors.mono fun out Hout => by
          rcases out with ⟨unit, targetEnv⟩
          rcases unit with ⟨⟩
          rcases Hout with ⟨_, ⟨Hconstructors⟩⟩
          exact ⟨trivial, ⟨{
            headerEnv := headerEnv
            header := Hheader
            constructors := Hconstructors }⟩⟩

structure ConstructorValidationConstructorFamilyStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (indType : InductiveType)
    (sourceEnv targetEnv : Environment) where
  oldInfo : InductiveVal
  lookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)
  constructors : ConstructorValidationStateTrace
    (ConstructorValidationConstructorStep result loweredEnv)
    oldInfo.ctors sourceEnv targetEnv

private theorem restoreInductiveConstructorsOnly_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (indType : InductiveType) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreInductiveConstructorsOnly result loweredEnv
      allowPrimitive indType sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty
          (ConstructorValidationConstructorFamilyStep result loweredEnv
            indType sourceEnv out.2) := by
  unfold Lean4Lean.restoreInductiveConstructorsOnly
  simp only [hlookup]
  have Hconstructors := constructorValidationForM_refines
    (fun ctorName => Lean4Lean.restoreConstructorDecl result loweredEnv
      allowPrimitive ctorName)
    (ConstructorValidationConstructorStep result loweredEnv)
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

structure RestoredConstructorValidationEnvironment
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (types : List InductiveType) (targetEnv : Environment) where
  headerEnv : Environment
  headers : ConstructorValidationStateTrace
    (fun indType source target => ConstructorValidationHeaderStep loweredEnv
      allIndNames indType.name source target)
    types sourceEnv headerEnv
  constructors : ConstructorValidationStateTrace
    (ConstructorValidationConstructorFamilyStep result loweredEnv)
    types headerEnv targetEnv

theorem restoreNestedConstructors_validationWF
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreNestedConstructors result loweredEnv allIndNames
      allowPrimitive types sourceEnv).WF fun out =>
        out.1 = () ∧ Nonempty (RestoredConstructorValidationEnvironment result
          loweredEnv sourceEnv allIndNames types out.2) := by
  unfold Lean4Lean.restoreNestedConstructors
  have Hheaders := constructorValidationForM_refines
    (fun indType => Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indType.name)
    (fun indType source target => ConstructorValidationHeaderStep loweredEnv
      allIndNames indType.name source target)
    types
    (fun indType hind currentEnv => by
      exact restoreInductiveHeaderDecl_validationWF loweredEnv currentEnv
        allIndNames allowPrimitive indType.name)
    sourceEnv
  exact Hheaders.bind fun out Hout => by
    rcases out with ⟨unit, headerEnv⟩
    rcases unit with ⟨⟩
    rcases Hout with ⟨_, ⟨Hheaders⟩⟩
    have Hconstructors := constructorValidationForM_refines
      (fun indType => Lean4Lean.restoreInductiveConstructorsOnly result
        loweredEnv allowPrimitive indType)
      (ConstructorValidationConstructorFamilyStep result loweredEnv)
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
