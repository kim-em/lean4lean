import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredBody
import Lean4Lean.Theory.Typing.AnchoredOriginalPayload
import Lean4Lean.Theory.Inductive.SaturatedNativeProgram

/-! Read the literal equation bodies from their original closed lambda
spines. Their natural typings and predecessor semantic payloads are retained;
no registered or declared result type is imposed by an inversion principle. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

structure OriginalTelescopeBody (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source domains : List VExpr) (body : VExpr) where
  natural : VExpr
  structural : Bool
  context : OnCtx (domains.reverse ++ source) (sourceEnv.IsType U)
  typing : sourceEnv.HasTypeStrong U (domains.reverse ++ source) body natural structural
  payload : OriginalPayload sourceEnv env U registry typing.refl

/-- Outer conversions are traversed by the original lambda-origin producer;
each recursive call selects the actual original body typing child. -/
theorem HasTypeStrong.originalTelescopeBody
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source : List VExpr} (hSource : OnCtx source (sourceEnv.IsType U))
    (domains : List VExpr) {body assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body) assigned structural) :
    Nonempty (OriginalTelescopeBody sourceEnv env U registry source domains body) := by
  induction domains generalizing source assigned structural with
  | nil => exact ⟨⟨assigned, structural, hSource, original, earlier original.refl⟩⟩
  | cons A domains ih =>
    obtain ⟨origin⟩ := HasTypeStrong.originalLambdaOrigin (fun H => (earlier H).joint) original rfl
    have nextContext : OnCtx (A :: source) (sourceEnv.IsType U) :=
      ⟨hSource, origin.domainLevel, origin.domainStrong.defeq⟩
    obtain ⟨next⟩ := ih nextContext origin.bodyTyping
    refine ⟨{
      natural := next.natural
      structural := next.structural
      context := ?_
      typing := ?_
      payload := ?_ }⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using next.context
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using next.typing
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using next.payload

structure NativeOriginalEquationBodies (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) {data : NativeRecursorData}
    (program : SaturatedProgram data) where
  left : OriginalTelescopeBody sourceEnv env U registry []
    (program.equationBody.domains.map (·.instL program.levels))
    (program.equationBody.lhs.instL program.levels)
  right : OriginalTelescopeBody sourceEnv env U registry []
    (program.equationBody.domains.map (·.instL program.levels))
    (program.equationBody.rhs.instL program.levels)

/-- The parser's actual selected equation identifies both lambda spines.
The result contains literal open Strong children, their semantic payloads,
and the original full source context formation. -/
theorem NativeRecursorData.originalEquationBodies
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural) :
    Nonempty (NativeOriginalEquationBodies sourceEnv env U registry program) := by
  have spec := saturatedProgram_spec selected
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have parsedLeft := left
  have parsedRight := right
  rw [← parts.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at parsedLeft
  rw [← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at parsedRight
  obtain ⟨leftBody⟩ := HasTypeStrong.originalTelescopeBody (source := []) earlier trivial _ parsedLeft
  obtain ⟨rightBody⟩ := HasTypeStrong.originalTelescopeBody (source := []) earlier trivial _ parsedRight
  exact ⟨⟨leftBody, rightBody⟩⟩

end Lean4Lean.AnchoredSource.Adapted
