import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedInputReplay

/-! Pull actual caller resource programs through the retained recipe context.
Each body program remains indexed by its original selected key. Resource
transfers substitute their actual finite variable traces; a fixed body does
not introduce a caller binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {Fits : Nat → Need → Prop}

/-- Replay the literal observations in a resource transfer, allowing each
input leaf to be supplied by a finite program instead of a literal Need. -/
noncomputable def RecipeResourceTransfer.replayVariablePrograms
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (rename : Nat → Nat)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      VariableDependencyProgram env U registry target Fits (rename i) need.profile) :
    ∀ i need, (i, need) ∈ required →
      VariableDependencyProgram env U registry target Fits (rename i) need.profile := by
  classical
  induction transfer with
  | nil => intro _ _ member; exact False.elim (List.not_mem_nil member)
  | @cons index used needed rest need query tail ih =>
    intro i requested member
    by_cases equal : (i, requested) = (index, need)
    · cases equal
      let trace : SortableVariableTrace env U registry target index need.profile used :=
        .legacy query.variableTrace
      exact SortableVariableTrace.replayPrograms henv hscoped formed trace (fun i requested member => by
        have program := supplied i requested (List.mem_append_left _ member)
        simpa only [trace.indices member] using program)
    · exact ih (fun i requested selected => supplied i requested
        (List.mem_append_right _ selected)) i requested ((List.mem_cons.mp member).resolve_left equal)

/-- A dependent transcript of the actual body keys in a retained context.
The index map records the effect of later genuine body binders. -/
noncomputable def RichRecipeContext.BinderPrograms
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (Fits : Nat → Need → Prop) (rename : Nat → Nat) : Type := by
  induction pending generalizing rename with
  | root => exact PUnit
  | domain pending ih | fixedBody pending selected admitted ih
      | resources pending transfer ih | action pending change ih => exact ih rename
  | @body source locals A B relevant prototypeDomain prototypeBody footprint σ n support result key rows
      parent pending selected anchor ih =>
    exact VariableDependencyProgram env U registry target Fits (rename 0) key.input ×
      ih (fun index => rename (index + 1))

/-- Construct the whole transcript in one traversal of the same context.
No semantic argument or body reply is supplied. -/
noncomputable def RichRecipeContext.binderPrograms
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (rename : Nat → Nat)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      VariableDependencyProgram env U registry target Fits (rename i) need.profile) :
    pending.BinderPrograms Fits rename := by
  induction pending generalizing rename with
  | root => exact PUnit.unit
  | domain pending ih | action pending change ih | fixedBody pending selected admitted ih =>
    exact ih rename supplied
  | body pending selected anchor ih =>
    exact ⟨supplied 0 _ List.mem_cons_self,
      ih (fun index => rename (index + 1)) (fun i need member => supplied (i + 1) need
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(i, need), member, rfl⟩)))⟩
  | resources pending transfer ih =>
    exact ih rename (transfer.replayVariablePrograms henv hscoped formed rename supplied)

/-- Public entry: only the actual final recipe footprint availability is
needed. Unions and other transfers may realize an earlier key using many
caller Needs; none of those earlier keys is asserted to occur literally. -/
noncomputable def RichRecipeContext.binderProgramsOfAvailable
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (resources : footprint.Available available) :
    pending.BinderPrograms (fun i need => need ∈ available i) id :=
  pending.binderPrograms henv hscoped formed id (fun index need member => {
    rank := need.rank, bound := Nat.le_refl _, raw := need.profile
    footprint := [(index, need)], trace := .legacy (.leaf need.profile)
    resources := by
      intro i requested selected
      cases List.mem_singleton.mp selected
      exact resources index need member
    adapter := by rw [raiseProfile_self]; exact .refl _ })

/-- A body occurrence records the key in the actual context and its current
caller index. Fixed bodies preserve indices; genuine bodies shift previous
occurrences. -/
inductive RichRecipeContext.BodyAt
    {input : RichRecipeRootInput env U registry target} :
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} →
    {expression : VExpr} → {relevant : Bool} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint} →
    RichRecipeContext input recipe → Nat → {m : Nat} → Key m → Type where
  | here {σ : Subst} {n : Nat} {support result : Profile n} {key : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (pending : RichRecipeContext input parent) (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
      BodyAt (.body pending selected anchor) 0 key
  | body {σ : Subst} {n : Nat} {support result : Profile n} {nextKey : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      {pending : RichRecipeContext input parent}
      (occurrence : BodyAt pending index key) (selected : (nextKey, result) ∈ rows)
      (anchor : nextKey.anchor = σ 0) :
      BodyAt (.body pending selected anchor) (index + 1) key
  | domain (occurrence : BodyAt pending index key) : BodyAt (.domain pending) index key
  | fixedBody {A B : VExpr} {n : Nat} {support result : Profile n} {nextKey : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      {pending : RichRecipeContext input parent}
      (occurrence : BodyAt pending index key) (selected : (nextKey, result) ∈ rows)
      (admitted : Admitted env U registry target nextKey anchor anchor) :
      BodyAt (.fixedBody pending selected admitted) index key
  | resources (occurrence : BodyAt pending index key) (transfer) :
      BodyAt (.resources pending transfer) index key
  | action (occurrence : BodyAt pending index key) (change) :
      BodyAt (.action pending change) index key

/-- Project a program from its exact syntactic occurrence. Neither key
equality nor an index is recovered from semantic readback. -/
noncomputable def RichRecipeContext.BodyAt.program
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe} {key : Key m}
    (occurrence : pending.BodyAt index key) (rename : Nat → Nat)
    (programs : pending.BinderPrograms Fits rename) :
    VariableDependencyProgram env U registry target Fits (rename index) key.input := by
  induction occurrence generalizing rename with
  | here => exact programs.1
  | body occurrence selected anchor ih => exact ih _ programs.2
  | domain occurrence ih | fixedBody occurrence selected admitted ih
      | resources occurrence transfer ih | action occurrence change ih => exact ih _ programs

noncomputable def RichRecipeContext.BodyAt.programOfAvailable
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe} {key : Key m}
    (occurrence : pending.BodyAt index key)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (resources : footprint.Available available) :
    VariableDependencyProgram env U registry target (fun i need => need ∈ available i) index key.input :=
  occurrence.program id (pending.binderProgramsOfAvailable henv hscoped formed resources)

/-- The actual ranked row continuation consumes precisely the key stored at
this body occurrence. Pad/down and input views are replayed after the caller
resource transfers, retaining the original native row's requested input. -/
noncomputable def RichRecipeContext.BodyAt.nativeInputProgram
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe} {key : Key m} {result : Profile m}
    {table : List (Key n × Profile n)}
    (occurrence : pending.BodyAt index key)
    (row : RankedPendingNativeRow env U registry target table relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (resources : footprint.Available available) :
    VariableDependencyProgram env U registry target (fun i need => need ∈ available i)
      index row.oldKey.input :=
  row.replayInput henv hscoped formed (occurrence.programOfAvailable henv hscoped formed resources)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
