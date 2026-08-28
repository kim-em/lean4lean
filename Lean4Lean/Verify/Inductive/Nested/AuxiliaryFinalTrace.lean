import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Final well-formedness evidence attached to the exact auxiliary semantic
restoration fold.  The two abstract environments are intentionally distinct:
recursors are typed in the canonical constructor environment, while restored
rules are typed in the final constant environment. -/
inductive RestoredAuxiliaryFinalWFTrace
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv recursorEnv ruleEnv : VEnv)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
        {Htrace : StateForMTrace
          (RestoredRecursorStep result loweredEnv auxRec allIndNames)
          names sourceEnv targetEnv}
        {priorRecursors : List VConstVal} {priorRules : List VDefEq}
        {finalRecursors : List VConstVal} {finalRules : List VDefEq},
      RestoredAuxiliarySemanticTrace decl block main safety trEnv Htrace
        priorRecursors priorRules finalRecursors finalRules →
      List VConstVal → List VDefEq → List VConstVal → List VDefEq → Prop
  | nil (sourceEnv : Environment) (recursors : List VConstVal)
      (rules : List VDefEq) :
      RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
        ruleEnv (.nil sourceEnv recursors rules) recursors rules recursors rules
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : StateForMTrace
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hsemantic : RestoredAuxiliaryStepSemantics decl block main safety trEnv
        Hstep priorRecursors)
      (Hrest : RestoredAuxiliarySemanticTrace decl block main safety trEnv
        Htail (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules)
      (Hrecursor : Hsemantic.recursor.toVConstant.WF recursorEnv)
      (Hrules : ∀ rule ∈ Hsemantic.rules, rule.WF ruleEnv)
      (Hfinal : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv
        recursorEnv ruleEnv Hrest
          (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules) :
      RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
        ruleEnv (.cons Hstep Htail Hsemantic Hrest) priorRecursors priorRules
          finalRecursors finalRules

theorem RestoredAuxiliaryFinalWFTrace.recursorsWF
    (H : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv
      recursorEnv ruleEnv Haux priorRecursors priorRules finalRecursors
        finalRules)
    (Hprior : ∀ recursor ∈ priorRecursors,
      recursor.toVConstant.WF recursorEnv) :
    ∀ recursor ∈ finalRecursors,
      recursor.toVConstant.WF recursorEnv :=
  match H with
  | .nil _ _ _ => Hprior
  | .cons _ _ Hsemantic _ Hrecursor _ Hfinal =>
    Hfinal.recursorsWF (by
      intro recursor hrecursor
      rcases List.mem_append.mp hrecursor with hprior | hnew
      · exact Hprior recursor hprior
      · have : recursor = Hsemantic.recursor := by simpa using hnew
        subst recursor
        exact Hrecursor)

theorem RestoredAuxiliaryFinalWFTrace.rulesWF
    (H : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv
      recursorEnv ruleEnv Haux priorRecursors priorRules finalRecursors
        finalRules)
    (Hprior : ∀ rule ∈ priorRules, rule.WF ruleEnv) :
    ∀ rule ∈ finalRules, rule.WF ruleEnv :=
  match H with
  | .nil _ _ _ => Hprior
  | .cons _ _ Hsemantic _ _ Hrules Hfinal =>
    Hfinal.rulesWF (by
      intro rule hrule
      rcases List.mem_append.mp hrule with hprior | hnew
      · exact Hprior rule hprior
      · exact Hrules rule hnew)

end VerifyInductive
end Lean4Lean
