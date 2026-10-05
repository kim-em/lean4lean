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

/-- Only constructors of the selected native owner are enumerated. -/
def constructorIndices (data : NativeRecursorData) :
    List (Fin data.schema.signature.constructors.size) :=
  (List.finRange data.schema.signature.constructors.size).filter
    (fun i => data.schema.signature.constructors[i].owner == data.owner)

theorem mem_constructorIndices {data : NativeRecursorData}
    {index : Fin data.schema.signature.constructors.size} :
    index ∈ data.constructorIndices ↔ data.schema.signature.constructors[index].owner = data.owner := by
  simp [constructorIndices]

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

/-- Successful compilation restores every generated rule, including every
rule of a nonsingleton native recursor. -/
theorem NativeRecursorRegistered.equation_exists (H : NativeRecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size) :
    ∃ equation, data.equation index = some equation := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hm : data.nativeInstance.equation index ∈ data.nativeInstance.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, _, he⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  exact ⟨equation, by simpa only [NativeRecursorData.equation, hr] using he⟩

/-- Rule presence follows from the actual installation, not from pattern
soundness or a guessed recursor name. -/
theorem NativeRecursorRegistered.equation_present (H : NativeRecursorRegistered env data)
    (hgen : data.equation index = some equation) : env.defeqs equation := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, hi, he⟩ :=
    registeredInstance H
  have hm : data.nativeInstance.equation index ∈ data.nativeInstance.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  have hg : (compilationRestoration source auxiliaries).equation
      (data.nativeInstance.equation index) = some equation := by
    simpa only [NativeRecursorData.equation, hr] using hgen
  cases Option.some.inj (hrestore.symm.trans hg)
  exact he.defeqs (VInductBlock.install_rule hi hmem)

theorem NativeRecursorRegistered.equation_uvars (_H : NativeRecursorRegistered env data)
    (hgen : data.equation index = some equation) : equation.uvars = data.uvars := by
  unfold NativeRecursorData.equation Restoration.equation at hgen
  simp only [bind, Option.bind_eq_some_iff] at hgen
  obtain ⟨_, _, _, _, _, _, he⟩ := hgen
  cases he
  rfl

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

/-- Constructor specialization computes the native major's actual name. -/
theorem NativeRecursorRegistered.equation_major (H : NativeRecursorRegistered env data)
    (hgen : data.equation index = some equation) :
    ∃ fn levels args, equation.lhs.stripLams = .app fn
      (VExpr.mkApps (.const (data.schema.restoration.headName
        data.schema.signature.constructors[index].name) levels) args) := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hg : (compilationRestoration source auxiliaries).equation
      (data.nativeInstance.equation index) = some equation := by
    simpa only [NativeRecursorData.equation, hr] using hgen
  simpa only [← hr] using Instance.restored_equation_major hdata index hg

/-- All syntax stored in the actual equation has the scope needed by fixed
pattern right-hand sides. -/
theorem NativeRecursorRegistered.equation_closed (henv : env.WF)
    (H : NativeRecursorRegistered env data) (hgen : data.equation index = some equation) :
    equation.lhs.Closed ∧ equation.rhs.Closed ∧ equation.type.Closed := by
  have hw := henv.ordered.defEqWF (H.equation_present hgen)
  obtain ⟨u, ht⟩ := hw.1.isType henv.ordered (by trivial)
  exact ⟨VExpr.WF.closedN henv.ordered ⟨_, hw.1⟩ (by trivial),
    VExpr.WF.closedN henv.ordered ⟨_, hw.2⟩ (by trivial),
    VExpr.WF.closedN henv.ordered (show VExpr.WF env equation.uvars [] equation.type from ⟨_, ht⟩) (by trivial)⟩


private theorem extracted_body_stripLams {lhs rhs type : VExpr}
    (H : CaseSchema.EquationBody.extract lhs rhs type = some body) :
    body.lhs.stripLams = body.lhs := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [CaseSchema.EquationBody.extract] at H
    obtain ⟨⟨rfl, rfl⟩, inner, hi, rfl⟩ := H
    exact ih (body := inner) hi
  | _ => simp only [CaseSchema.EquationBody.extract, Option.some.injEq] at H; cases H; rfl

private theorem stripLams_wrapLams (domains : List VExpr) (expr : VExpr) :
    (VExpr.wrapLams domains expr).stripLams = expr.stripLams := by
  induction domains with
  | nil => rfl
  | cons _ _ ih => exact ih

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
  rw [← (CaseSchema.EquationBody.extract_sound hbody).1, stripLams_wrapLams, extracted_body_stripLams hbody] at he
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
