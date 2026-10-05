import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming
import Lean4Lean.Theory.Typing.CanonicalHeadRegistryData

/-! A deterministic syntax fragment for common head displays: head beta,
ordinary registered definitions, and saturated native singleton programs.
Native proof binders grow the context; trailing applications are preserved.
Neither typing guards nor their availability select an alternative step.

This is not the full final-calculus head machine. Ordinary constructor iota,
quotient computation, abstract eliminators and projections are not dispatched
here. Typed guard production and soundness of these traces are separate.
-/

namespace Lean4Lean.CanonicalHead
open VExpr InductiveSignature NativeRecursorData

structure Output where
  added : List VExpr
  result : VExpr

def Output.rename (out : Output) (ρ : Lift) : Output := {
  added := renameAdded ρ out.added
  result := out.result.lift' (ρ.consN out.added.length) }

def nativeOutput (data : NativeRecursorData) (levels : List VLevel)
    (arguments : List VExpr) : Option Output :=
  (data.saturatedProgram levels arguments).map fun program =>
    ⟨program.state.added, program.result⟩

/-- The first application of a lambda contracts, retaining all later args.
An existing definition entry has priority over native lookup; failure of any
structural check leaves the head stuck, rather than selecting another rule. -/
def spineStep (registry : Registry) : VExpr → List VExpr → Option Output
  | .lam _ body, argument :: trailing =>
    some ⟨[], mkApps (body.inst argument) trailing⟩
  | .const name levels, arguments =>
    match registry.definitions name with
    | some value =>
      if value.name = name ∧ levels.length = value.uvars then
        some ⟨[], mkApps (value.value.instL levels) arguments⟩
      else none
    | none =>
      match registry.natives name with
      | some data =>
        if data.name = name then nativeOutput data levels arguments else none
      | none => none
  | _, _ => none

def step (registry : Registry) (expression : VExpr) : Option Output :=
  spineStep registry expression.getAppFnArgs.1 expression.getAppFnArgs.2

/-- The exact syntactic origin of a selected step, with no typing premise. -/
inductive Origin (registry : Registry) : VExpr → List VExpr → Output → Prop where
  | beta : Origin registry (.lam domain body) (argument :: trailing)
      ⟨[], mkApps (body.inst argument) trailing⟩
  | delta {name : Name} {levels : List VLevel} {value : VDefVal} :
      registry.definitions name = some value →
      value.name = name → levels.length = value.uvars →
      Origin registry (.const name levels) arguments
        ⟨[], mkApps (value.value.instL levels) arguments⟩
  | native {name : Name} {levels : List VLevel} {data : NativeRecursorData}
      {program : SaturatedProgram data} :
      registry.definitions name = none → registry.natives name = some data →
      data.name = name → data.saturatedProgram levels arguments = some program →
      Origin registry (.const name levels) arguments ⟨program.state.added, program.result⟩

theorem spineStep_origin {registry : Registry} {head : VExpr} {arguments : List VExpr}
    {out : Output} (h : spineStep registry head arguments = some out) :
    Origin registry head arguments out := by
  cases head <;> simp only [spineStep] at h <;> try contradiction
  case const name levels =>
    split at h
    · rename_i value hvalue
      split at h <;> try contradiction
      rename_i hchecks
      cases h
      exact .delta hvalue hchecks.1 hchecks.2
    · rename_i hdefinition
      split at h <;> try contradiction
      rename_i data hdata
      split at h <;> try contradiction
      rename_i hname
      simp only [nativeOutput, Option.map_eq_some_iff] at h
      obtain ⟨program, hp, h⟩ := h
      cases h
      exact .native hdefinition hdata hname hp
  case lam domain body =>
    cases arguments <;> simp only at h <;> try contradiction
    cases h
    exact .beta

theorem step_origin {registry : Registry} {expression : VExpr} {out : Output}
    (h : step registry expression = some out) :
    Origin registry expression.getAppFnArgs.1 expression.getAppFnArgs.2 out :=
  spineStep_origin h

@[simp] theorem step_pi (registry : Registry) (A B : VExpr) :
    step registry (.forallE A B) = none := rfl

@[simp] theorem step_sort (registry : Registry) (u : VLevel) :
    step registry (.sort u) = none := rfl

private theorem mkApps_rename (head : VExpr) (arguments : List VExpr) (ρ : Lift) :
    (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument trailing ih => exact ih (.app head argument)

private theorem spine_rename (expression : VExpr) (ρ : Lift) :
    (expression.lift' ρ).getAppFnArgs =
      (expression.getAppFnArgs.1.lift' ρ, expression.getAppFnArgs.2.map (·.lift' ρ)) := by
  suffices ∀ args, getAppFnArgs.go (expression.lift' ρ) (args.map (·.lift' ρ)) =
      ((getAppFnArgs.go expression args).1.lift' ρ,
        (getAppFnArgs.go expression args).2.map (·.lift' ρ)) from this []
  induction expression with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

theorem nativeOutput_rename {data : NativeRecursorData}
    (hc : ∀ equation, data.singletonEquation = some equation → equation.rhs.Closed)
    (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    nativeOutput data levels (arguments.map (·.lift' ρ)) =
      (nativeOutput data levels arguments).map (·.rename ρ) := by
  cases hp : data.saturatedProgram levels arguments with
  | some program =>
    have hequation := (saturatedProgram_spec hp).2.2.2.2.2.2.2.2.1
    obtain ⟨hr, _, _, hout⟩ := saturatedProgram_rename_of_closed_rhs hp
      ((hc _ hequation).instL (ls := levels)) ρ
    simp only [nativeOutput, hp, hr, Option.map_some]
    simp only [SaturatedProgram.rename, SaturatedCaptureState.rename, Output.rename]
    exact congrArg (fun result => some (Output.mk (renameAdded ρ program.state.added) result)) hout
  | none =>
    cases hr : data.saturatedProgram levels (arguments.map (·.lift' ρ)) with
    | none => simp [nativeOutput, hp, hr]
    | some program =>
      obtain ⟨_, _, _, _, _, _, _, _, heq, hb, _, _, _, _⟩ := saturatedProgram_spec hr
      have hs := (scope_of_extract hb (hc _ heq)).1
      rw [saturatedProgram_rename_eq heq hb hs levels arguments ρ, hp] at hr
      contradiction

theorem spineStep_rename {registry : Registry} (hc : registry.Scoped)
    (head : VExpr) (arguments : List VExpr) (ρ : Lift) :
    spineStep registry (head.lift' ρ) (arguments.map (·.lift' ρ)) =
      (spineStep registry head arguments).map (·.rename ρ) := by
  cases head <;> try rfl
  case lam domain body =>
    cases arguments with
    | nil => rfl
    | cons argument trailing =>
      simp only [lift', List.map_cons, spineStep, Option.map_some, Output.rename,
        renameAdded, List.length_nil, Lift.consN, mkApps_rename, lift'_inst_hi]
  case const name levels =>
    simp only [lift', spineStep]
    cases hd : registry.definitions name with
    | some value =>
      simp only
      split
      · have hv : (value.value.instL levels).lift' ρ = value.value.instL levels :=
          (hc.definition _ _ hd).instL.lift'_eq Lift.Fixes.zero
        simp only [Option.map_some, Output.rename, renameAdded, List.length_nil,
          Lift.consN, mkApps_rename, hv]
      · rfl
    | none =>
      simp only
      cases hn : registry.natives name with
      | none => rfl
      | some data =>
        simp only
        split
        · exact nativeOutput_rename (hc.native _ _ hn) levels arguments ρ
        · rfl

/-- Renaming preserves both the selected step and its fresh proof slots.
This is total naturality, including structural failure/stuckness. -/
theorem step_rename {registry : Registry} (hc : registry.Scoped)
    (expression : VExpr) (ρ : Lift) :
    step registry (expression.lift' ρ) = (step registry expression).map (·.rename ρ) := by
  unfold step
  rw [spine_rename]
  exact spineStep_rename hc _ _ _

/-- Finite traces retain their complete added telescope in context order.
The relation permits stopping anywhere; terminal comparison below ensures
that a literal Pi/sort is the first such head reached. -/
inductive Trace (registry : Registry) : VExpr → List VExpr → VExpr → Prop where
  | refl : Trace registry expression [] expression
  | next : step registry expression = some out →
      Trace registry out.result added result →
      Trace registry expression (added ++ out.added) result

theorem Trace.terminal_unique {registry : Registry}
    {expression left right : VExpr} {addedLeft addedRight : List VExpr}
    (h : Trace registry expression addedLeft left)
    (h' : Trace registry expression addedRight right)
    (hl : step registry left = none) (hr : step registry right = none) :
    addedLeft = addedRight ∧ left = right := by
  induction h generalizing addedRight right with
  | refl =>
    cases h' with
    | refl => exact ⟨rfl, rfl⟩
    | next hs _ => rw [hl] at hs; contradiction
  | @next expression out added result hs ht ih =>
    cases h' with
    | refl => rw [hr] at hs; contradiction
    | @next _ other otherAdded otherResult hs' ht' =>
      have ho : out = other := Option.some.inj (hs.symm.trans hs')
      cases ho
      obtain ⟨ha, he⟩ := ih ht' hl hr
      exact ⟨congrArg (· ++ out.added) ha, he⟩

theorem Trace.pi_unique {registry : Registry}
    (h : Trace registry expression added (.forallE A B))
    (h' : Trace registry expression added' (.forallE A' B')) :
    added = added' ∧ A = A' ∧ B = B' := by
  obtain ⟨ha, he⟩ := h.terminal_unique h' (step_pi ..) (step_pi ..)
  cases he
  exact ⟨ha, rfl, rfl⟩

theorem Trace.sort_unique {registry : Registry}
    (h : Trace registry expression added (.sort u))
    (h' : Trace registry expression added' (.sort v)) : added = added' ∧ u = v := by
  obtain ⟨ha, he⟩ := h.terminal_unique h' (step_sort ..) (step_sort ..)
  cases he
  exact ⟨ha, rfl⟩

theorem renameAdded_append (ρ : Lift) (newer older : List VExpr) :
    renameAdded ρ (newer ++ older) =
      renameAdded (ρ.consN older.length) newer ++ renameAdded ρ older := by
  induction newer with
  | nil => rfl
  | cons domain rest ih =>
    simp only [List.cons_append, renameAdded, List.length_append, Lift.consN_consN, ih]
    rw [Nat.add_comm rest.length older.length]

/-- Existing private context insertions rename, while each proof slot created
by the trace remains a fresh binder on both sides. -/
theorem Trace.rename {registry : Registry} (hc : registry.Scoped)
    {expression result : VExpr} {added : List VExpr}
    (h : Trace registry expression added result) (ρ : Lift) :
    Trace registry (expression.lift' ρ) (renameAdded ρ added)
      (result.lift' (ρ.consN added.length)) := by
  induction h generalizing ρ with
  | @refl expression =>
    simpa [renameAdded] using Trace.refl (registry := registry) (expression := expression.lift' ρ)
  | @next expression out added result hs ht ih =>
    have hs' : step registry (expression.lift' ρ) = some (out.rename ρ) := by
      rw [step_rename hc, hs]
      rfl
    have h := Trace.next hs' (ih (ρ.consN out.added.length))
    simpa only [Output.rename, renameAdded_append, List.length_append, Lift.consN_consN,
      Nat.add_comm out.added.length added.length] using h

/-- Compare a renamed successful Pi trace with any other successful Pi trace
from that same renamed source. Domains and bodies agree as literal syntax. -/
theorem Trace.pi_unique_renamed {registry : Registry} (hc : registry.Scoped)
    (h : Trace registry expression added (.forallE A B)) (ρ : Lift)
    (h' : Trace registry (expression.lift' ρ) added' (.forallE A' B')) :
    renameAdded ρ added = added' ∧
      A.lift' (ρ.consN added.length) = A' ∧
      B.lift' (ρ.consN added.length).cons = B' :=
  (h.rename hc ρ).pi_unique h'

end Lean4Lean.CanonicalHead
