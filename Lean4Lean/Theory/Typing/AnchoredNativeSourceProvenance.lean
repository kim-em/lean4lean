import Lean4Lean.Theory.Typing.SourceConstantProvenance
import Lean4Lean.Theory.Typing.NativeRegistryPrefix
import Lean4Lean.Theory.Typing.AnchoredNativeSyntax

/-! Source provenance of every fixed native child. These facts use the
original pre-equation Strong roots retained by the concrete registry history;
final registration alone would not identify this earlier source environment. -/
namespace Lean4Lean
open VExpr InductiveSignature NativeRecursorData
namespace VEnv.NativeDeclarationOrigin
variable {base : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
  {type domain : VExpr} {equation : VDefEq} {levels : List VLevel}
  {index : Nat} {instruction : CaptureInstruction}

theorem typeConstants (origin : NativeDeclarationOrigin base declarations data)
    (selected : data.recursorType = some type) : type.ConstantsIn base := by
  obtain ⟨level, original⟩ := origin.typeStrong selected
  exact original.constantsIn.1.mono
    (origin.stage.typing.recursors_le.trans origin.stage.installedBelow)

theorem singletonConstants (origin : NativeDeclarationOrigin base declarations data)
    (selected : data.singletonEquation = some equation) : equation.rhs.ConstantsIn base :=
  (origin.singletonStrong selected).2.constantsIn.1.mono
    (origin.stage.typing.recursors_le.trans origin.stage.installedBelow)

theorem signatureDomainConstants (origin : NativeDeclarationOrigin base declarations data)
    (signature : AnchoredSource.Adapted.NativeConstantSignature data levels)
    (member : signature.domains[index]? = some domain) : domain.ConstantsIn base :=
  ((origin.typeConstants signature.typeOrigin).instL levels).takeForalls signature.telescope |>.1
    domain (List.mem_of_getElem? member)

theorem programConstants (origin : NativeDeclarationOrigin base declarations data)
    {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program) :
    (∀ domain ∈ program.equationBody.domains, domain.ConstantsIn base) ∧
      program.equationBody.rhs.ConstantsIn base := by
  have spec := saturatedProgram_spec selected
  have known := origin.singletonConstants spec.2.2.2.2.2.2.2.2.1
  have extracted := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  exact (extracted.2.1.symm ▸ known).wrapLams

theorem instructionConstants (origin : NativeDeclarationOrigin base declarations data)
    {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program)
    (member : program.instructions[index]? = some instruction) : instruction.domain.ConstantsIn base := by
  have spec := saturatedProgram_spec selected
  have domainMember : instruction.domain ∈ program.instructions.map CaptureInstruction.domain :=
    List.mem_map.mpr ⟨instruction, List.mem_of_getElem? member, rfl⟩
  rw [spec.2.2.2.2.2.2.2.2.2.2.1, fieldInstructions_domains] at domainMember
  obtain ⟨domain, member, equal⟩ := List.mem_map.mp domainMember
  rw [← equal]
  exact ((origin.programConstants selected).1 domain (List.mem_of_mem_drop member)).instL levels

theorem indexConstants (origin : NativeDeclarationOrigin base declarations data)
    {program : SaturatedProgram data} (templates : AnchoredSource.Adapted.NativeIndexTemplates program) :
    templates.naturalDomain.ConstantsIn base ∧ templates.declaredDomain.ConstantsIn base := by
  constructor
  · exact (((origin.typeConstants templates.registeredType).instL program.levels).takeForalls
      templates.telescope).1 _ (List.mem_of_getElem? templates.naturalOrigin)
  · exact origin.instructionConstants templates.selected templates.declaredOrigin

end VEnv.NativeDeclarationOrigin
end Lean4Lean
