import Lean4Lean.Theory.Typing.AnchoredSupport
import Lean4Lean.Theory.Typing.AnchoredExposureComparison
import Lean4Lean.Theory.Typing.AnchoredFunctionIntroduction
import Lean4Lean.Theory.Typing.AnchoredReanchor

/-! Extend an input demand using separately supplied evidence for the actual
assigned type. Unlike a computed type view, this operation does not pretend
that a larger input's code can be obtained from the old smaller input. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem input_subset_rename {old new : Profile n}
    (subset : List.Subset old new) (ρ : Lift) :
    List.Subset (old.rename ρ) (new.rename ρ) := by
  intro atom hm
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map.mpr ⟨original, subset member, rfl⟩

theorem Admitted.restrictInput {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {input : Profile n}
    (subset : List.Subset key.input input)
    (admitted : Admitted env U registry Γ (inputKey key input) x y) :
    Admitted env U registry Γ key x y := by
  obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := admitted
  have oldTyped : key.input.HasType support := by
    cases n with
    | zero => exact fun atom hm => typed atom (subset hm)
    | succ n => exact ⟨fun atom hm => typed.1 atom (subset hm), typed.2.1,
        fun atom hm => typed.2.2 atom (subset hm)⟩
  exact ⟨raw, pair, support, oldTyped, formed, code,
    Related.of_singletons (fun _ hm => Related.singleton_of_mem first (subset hm)),
    Related.of_singletons (fun _ hm => Related.singleton_of_mem second (subset hm))⟩

theorem FunctionBehavior.extendInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {oldTypeProfile newTypeProfile : Profile (n + 1)} {input : Profile n}
    (henv : env.Ordered)
    (subset : List.Subset key.input input)
    (seed : Admitted env U registry Γ (inputKey key input) key.anchor key.anchor)
    (hnew : TypeRelated env U registry Γ type type newTypeProfile)
    (htyped : (Profile.fn (inputKey key input) output).HasType newTypeProfile)
    (hold : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output oldTypeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type (inputKey key input) output newTypeProfile := by
  obtain ⟨_, hold⟩ := hold
  refine ⟨seed, ?_⟩
  obtain ⟨oldA, oldB, oldDom, oldRows, oldResult, _, oldRow, oldTyped,
    oldDisplay, oldBehavior⟩ := hold
  obtain ⟨newA, newB, newDom, newRows, newResult, newMem, _, _, _, newRow, newTyped⟩ :=
    htyped.fn_inv (List.mem_singleton_self _)
  change Profile n at newDom newResult
  change List (Key n × Profile n) at newRows
  have hΓ := oldDisplay.leftExposure.generated.baseWF
  have hcore := hnew Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at hcore
  obtain ⟨newDisplay⟩ := hcore _ newMem
  refine ⟨newA, newB, newDom, newRows, newResult, newMem, newRow, newTyped,
    newDisplay, ?_⟩
  intro V τ future x y admitted
  obtain ⟨C, i, j, oldInsertion, newInsertion, hmaps, _, hbodies⟩ :=
    oldDisplay.leftExposure.samePi newDisplay.leftExposure henv
  obtain ⟨W, α, β, proof, extension, hpush⟩ := newInsertion.pushout future henv
  obtain ⟨oldW, oldFuture, changed⟩ := oldInsertion.pullFuture henv extension
  have hmap : oldDisplay.map.comp (i.comp β) = (newDisplay.map.comp τ).comp α := by
    rw [← Lift.comp_assoc, hmaps, Lift.comp_assoc, hpush, ← Lift.comp_assoc]
  have hbody : oldDisplay.leftBody.lift' (i.comp β).cons =
      newDisplay.leftBody.lift' (τ.comp α).cons := by
    calc
      _ = (oldDisplay.leftBody.lift' i.cons).lift' β.cons := lift'_comp
      _ = (newDisplay.leftBody.lift' j.cons).lift' β.cons := congrArg (·.lift' β.cons) hbodies
      _ = newDisplay.leftBody.lift' (j.comp β).cons := lift'_comp.symm
      _ = _ := congrArg (fun ρ => newDisplay.leftBody.lift' ρ.cons) hpush
  have htype : (oldDisplay.leftBody.lift' (i.comp β).cons).inst (x.lift' α) =
      ((newDisplay.leftBody.lift' τ.cons).inst x).lift' α := by
    rw [hbody, lift'_inst_hi, ← lift'_comp]
    rfl
  have harg : Admitted env U registry W (key.rename (oldDisplay.map.comp (i.comp β)))
      (x.lift' α) (y.lift' α) := by
    have admitted' : Admitted env U registry V
        (inputKey (key.rename (newDisplay.map.comp τ))
          (input.rename (newDisplay.map.comp τ))) x y := admitted
    have restricted := Admitted.restrictInput
      (key := key.rename (newDisplay.map.comp τ)) (input_subset_rename subset _) admitted'
    simpa only [← Key.rename_comp, hmap] using
      proof.admitted henv restricted
  have oldArg := (changed.symm henv).admitted henv harg
  obtain ⟨oldLeft, oldRight, oldCross⟩ :=
    oldBehavior oldW (i.comp β) oldFuture (x.lift' α) (y.lift' α) oldArg
  have oldOutputs := And.intro (changed.term henv oldLeft)
    (And.intro (changed.term henv oldRight) (changed.term henv oldCross))
  have newCode : TypeRelated env U registry W
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      ((newResult.rename (newDisplay.map.comp τ)).rename α) :=
    proof.code henv (TypeRelated.left_diagonal
      (newDisplay.rowBodies (inputKey key input) newResult newRow V τ future x y admitted).1)
  have newValueTyped := (Profile.rename_hasType_iff
    (ρ := (newDisplay.map.comp τ).comp α)).mpr newTyped
  simp only [Profile.rename_singleton] at newValueTyped
  simp only [hmap, htype] at oldOutputs
  rw [← Profile.rename_comp] at newCode
  obtain ⟨hleft, hright, hpair⟩ := oldOutputs
  have hleft' := Related.retag henv newValueTyped newCode hleft
  have hright' := Related.retag henv newValueTyped newCode hright
  have hpair' := Related.retag henv newValueTyped newCode hpair
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hleft'
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hright'
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hpair'

/-- A larger input is sound at any assigned type when its actual code is
supplied separately. This theorem has no literal-Pi or source-typing premise;
the two chosen displays are compared by their common actual type. -/
theorem Related.extendInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {input : Profile n} {oldSupport newSupport : Profile (n + 1)}
    (henv : env.Ordered) (subset : List.Subset key.input input)
    (seed : Admitted env U registry Γ (inputKey key input) key.anchor key.anchor)
    (typed : (Profile.fn (inputKey key input) output).HasType newSupport)
    (code : TypeRelated env U registry Γ type type newSupport)
    (related : Related env U registry Γ left right type (Profile.fn key output) oldSupport) :
    Related env U registry Γ left right type
      (Profile.fn (inputKey key input) output) newSupport := by
  intro requested member Δ ρ future
  cases List.mem_singleton.mp member
  have old := related (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases old with hempty | ⟨Ω, τ, insertion, oldTyped, oldCode, values⟩
  · cases hempty
  · have full := future.comp insertion.toFuture henv
    have subset' := input_subset_rename subset (ρ.comp τ)
    have typed' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr typed
    have code' := code.future henv full
    have seed' := seed.future henv full
    simp only [lift'_comp, Profile.rename_comp] at subset' typed' code' seed'
    simp only [Key.rename, inputKey, lift'_comp, Profile.rename_comp] at seed'
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((newSupport.rename ρ).rename τ) at code'
    change (Profile.fn (inputKey ((key.rename ρ).rename τ) ((input.rename ρ).rename τ))
      ((output.rename ρ).rename τ)).HasType ((newSupport.rename ρ).rename τ) at typed'
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have changed := FunctionBehavior.extendInput henv subset' seed' code' typed' behavior
    right
    refine ⟨Ω, τ, insertion, ?_, code', ?_⟩
    · simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Key.rename,
        inputKey] using typed'
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [TermAtom, Atom.rename_fn, inputKey, Key.rename] using changed

end Lean4Lean.AnchoredSemantics
