import Lean4Lean.Theory.Typing.CanonicalHeadApplication
import Lean4Lean.Theory.Inductive.SaturatedNativeSubstitution

/-! Existing successful canonical traces commute with raw substitution.
New native proof binders are retained. The theorem is forward only: an
arbitrary substitution can make a previously stuck variable reducible. -/
namespace Lean4Lean.CanonicalHead
open VExpr InductiveSignature NativeRecursorData
open private rebuild_spine from Lean4Lean.Theory.Inductive.CaseReductionData
set_option backward.isDefEq.respectTransparency false

def Output.subst (out : Output) (σ : Subst) : Output := {
  added := substAdded σ out.added
  result := out.result.subst (σ.liftN out.added.length) }

private theorem spine_mkApps (head : VExpr) (arguments : List VExpr) :
    (mkApps head arguments).getAppFnArgs =
      (head.getAppFnArgs.1, head.getAppFnArgs.2 ++ arguments) := by
  induction arguments generalizing head with
  | nil => simp [mkApps]
  | cons argument rest ih =>
    change (mkApps (.app head argument) rest).getAppFnArgs = _
    rw [ih, getAppFnArgs_app]
    simp only [List.append_assoc, List.singleton_append]

/-- Scope and successful parser evidence suffice even for non-variable
substitutions. The native major and all trailing arguments remain explicit. -/
theorem spineStep_subst {registry : Registry} (scope : registry.Scoped)
    {head : VExpr} {arguments : List VExpr} {out : Output}
    (selected : spineStep registry head arguments = some out) (σ : Subst) :
    spineStep registry (head.subst σ) (arguments.map (·.subst σ)) = some (out.subst σ) := by
  cases spineStep_origin selected with
  | beta =>
    simp only [VExpr.subst, List.map_cons, spineStep, Output.subst, substAdded,
      List.length_nil, Subst.liftN, subst_mkApps, subst_inst]
  | delta lookup named length =>
    rename_i name levels value
    have closed : (value.value.instL levels).subst σ = value.value.instL levels :=
      (scope.definition _ _ lookup).instL.subst_eq .zero
    simp only [VExpr.subst, spineStep, lookup, named, length, and_self, ↓reduceIte,
      Output.subst, substAdded, List.length_nil, Subst.liftN, subst_mkApps, closed]
  | native definition native named program =>
    have equation := (saturatedProgram_spec program).2.2.2.2.2.2.2.2.1
    obtain ⟨changed, _, _, result⟩ := saturatedProgram_subst_of_closed_rhs program
      (scope.native _ _ native _ equation) σ
    simp only [VExpr.subst, spineStep, definition, native, named, ↓reduceIte,
      nativeOutput, changed, Option.map_some, Output.subst]
    simp only [SaturatedProgram.subst, SaturatedCaptureState.subst] at result ⊢
    exact congrArg (fun e => some (Output.mk _ e)) result

private theorem Origin.subst_spine {registry : Registry} {head : VExpr}
    {arguments : List VExpr} {out : Output}
    (origin : Origin registry head arguments out) (σ : Subst) :
    (head.subst σ).getAppFnArgs = (head.subst σ, []) := by
  cases origin <;> rfl

/-- An already selected step has a non-variable head; substitution preserves
its whole application spine. No claim is made about unselected expressions. -/
theorem step_subst {registry : Registry} (scope : registry.Scoped)
    {expression : VExpr} {out : Output}
    (selected : step registry expression = some out) (σ : Subst) :
    step registry (expression.subst σ) = some (out.subst σ) := by
  have moved := spineStep_subst scope selected σ
  have rebuilt := (rebuild_spine expression).symm
  rw [rebuilt, subst_mkApps, step, spine_mkApps]
  rw [(step_origin selected).subst_spine]
  simpa only [List.nil_append] using moved

private theorem subst_liftN_add (σ : Subst) (a b : Nat) :
    (σ.liftN a).liftN b = σ.liftN (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Subst.liftN, ih]; rfl

theorem substAdded_append (σ : Subst) (newer older : List VExpr) :
    substAdded σ (newer ++ older) =
      substAdded (σ.liftN older.length) newer ++ substAdded σ older := by
  induction newer with
  | nil => rfl
  | cons domain rest ih =>
    simp only [List.cons_append, substAdded, List.length_append, subst_liftN_add, ih]
    rw [Nat.add_comm rest.length older.length]

/-- Exact forward substitution of the successful trace, including its
complete fresh telescope and the final term below those fresh binders. -/
theorem Trace.subst {registry : Registry} (scope : registry.Scoped)
    {expression result : VExpr} {added : List VExpr}
    (trace : Trace registry expression added result) (σ : Subst) :
    Trace registry (expression.subst σ) (substAdded σ added)
      (result.subst (σ.liftN added.length)) := by
  induction trace generalizing σ with
  | refl => exact .refl
  | @next expression out added result selected rest ih =>
    have next := Trace.next (step_subst scope selected σ) (ih (σ.liftN out.added.length))
    simpa only [Output.subst, substAdded_append, List.length_append, subst_liftN_add,
      Nat.add_comm out.added.length added.length] using next

end Lean4Lean.CanonicalHead
