import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Inductive.NativeEquationOrigin
import Batteries.Tactic.OpenPrivate

/-! Every native rule is selected from the same finite compilation instance
as its recursor. Restoration, equation presence and head ownership are
retained before constructing the corresponding first-order pattern. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

/-- The exact restored native equation at a signature constructor index. -/
def equation (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) : Option VDefEq :=
  data.schema.restoration.equation (data.nativeInstance.equation index)

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open InductiveSignature
open private rebuild_spine from Lean4Lean.Theory.Inductive.CaseReductionData
variable {data : NativeRecursorData} {equation : VDefEq}
  {index : Fin data.schema.signature.constructors.size}

private theorem registeredInstance (H : NativeRecursorRegistered env data) :
    ∃ base installBase source expanded auxiliaries block installed,
      CompilationData base source expanded data.schema.signature data.nativeInstance auxiliaries block ∧
      CertifiedSpecializations base auxiliaries ∧
      data.schema.restoration = compilationRestoration source auxiliaries ∧
      block.install installBase = some installed ∧ installed ≤ env := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hg : data.nativeInstance = g := by
    cases g
    simp only [NativeRecursorData.nativeInstance, Instance.mk.injEq]
    exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  exact ⟨base, installBase, source, expanded, auxiliaries, block, installed, hg ▸ hdata, hprior, hr, hi, he⟩

/-- The restored equation is headed by precisely this native recursor. -/
theorem NativeRecursorRegistered.equation_head (H : NativeRecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) :
    equation.lhs.stripLams.getAppFnArgs.1 = .const data.name (VLevel.params data.uvars) := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hleft := (Restoration.equation_parts hgen).1
  have hn := hdata.heads_not_recursors data.schema.signature.constructors[index].owner
  rw [← hr] at hn
  have he := Restoration.wrapLams_head_const hn
    (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  simpa only [NativeRecursorData.nativeInstance, NativeRecursorData.name,
    Instance.recursorName, howner] using he

private theorem extracted_body_stripLams {lhs rhs type : VExpr}
    (H : CaseSchema.EquationBody.extract lhs rhs type = some body) :
    body.lhs.stripLams = body.lhs := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [CaseSchema.EquationBody.extract] at H
    obtain ⟨⟨rfl, rfl⟩, inner, hi, rfl⟩ := H
    exact ih (body := inner) hi
  | _ => simp only [CaseSchema.EquationBody.extract, Option.some.injEq] at H; cases H; rfl

/-- Every extracted native equation body has an actual constant head. -/
theorem NativeRecursorRegistered.equation_body_head
    (H : NativeRecursorRegistered env data) (hgen : data.equation index = some equation)
    (hbody : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body) :
    ∃ name levels args, body.lhs = VExpr.mkApps (.const name levels) args := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hleft := (Restoration.equation_parts hgen).1
  have hn := hdata.heads_not_recursors data.schema.signature.constructors[index].owner
  rw [← hr] at hn
  have he := Restoration.wrapLams_head_const hn
    (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  rw [← (CaseSchema.EquationBody.extract_sound hbody).1, VExpr.stripLams_wrapLams, extracted_body_stripLams hbody] at he
  exact ⟨_, _, body.lhs.getAppFnArgs.2, by
    rw [← he]
    exact (rebuild_spine body.lhs).symm⟩

theorem NativeRecursorRegistered.singletonEquation_body_head
    (H : NativeRecursorRegistered env data) (hgen : data.singletonEquation = some equation)
    (hbody : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body) :
    ∃ name levels args, body.lhs = VExpr.mkApps (.const name levels) args := by
  unfold NativeRecursorData.singletonEquation at hgen
  dsimp only at hgen
  split at hgen <;> try contradiction
  exact H.equation_body_head hgen hbody

end Lean4Lean.VEnv
