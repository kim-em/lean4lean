import Lean4Lean.Theory.Typing.AnchoredFrame
import Lean4Lean.Theory.Typing.AnchoredDiagonal
import Lean4Lean.Theory.Typing.AnchoredExposureComparison
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

/-! Change the type support of one actual function capability. The old and
new Pi displays are constructed witnesses, and their common proof extension
is produced by canonical trace comparison. Only the lower-rank support-change
induction hypothesis is assumed.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem FunctionBehavior.retag
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {oldTypeProfile newTypeProfile : Profile (n + 1)}
    (henv : env.Ordered)
    (lowerIH : ∀ Γ a b A (p d d₀ : Profile n),
      p.HasType d → p.HasType d₀ →
      TypeRelated env U registry Γ A A d → TypeRelated env U registry Γ A A d₀ →
      Related env U registry Γ a b A p d → Related env U registry Γ a b A p d₀)
    (hnew : TypeRelated env U registry Γ type type newTypeProfile)
    (htyped : (Profile.fn key output).HasType newTypeProfile)
    (hold : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output oldTypeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output newTypeProfile := by
  obtain ⟨anchorAdmitted, hold⟩ := hold
  refine ⟨anchorAdmitted, ?_⟩
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
    simpa only [← Key.rename_comp, hmap] using
      proof.admitted henv admitted
  have oldArg := (changed.symm henv).admitted henv harg
  obtain ⟨oldLeft, oldRight, oldCross⟩ :=
    oldBehavior oldW (i.comp β) oldFuture (x.lift' α) (y.lift' α) oldArg
  have oldOutputs := And.intro (changed.term henv oldLeft)
    (And.intro (changed.term henv oldRight) (changed.term henv oldCross))
  have oldCode := changed.code henv (TypeRelated.left_diagonal
    (oldDisplay.rowBodies key oldResult oldRow oldW (i.comp β) oldFuture
      (x.lift' α) (y.lift' α) oldArg).1)
  have newCode : TypeRelated env U registry W
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      ((newResult.rename (newDisplay.map.comp τ)).rename α) :=
    proof.code henv (TypeRelated.left_diagonal
      (newDisplay.rowBodies key newResult newRow V τ future x y admitted).1)
  have oldValueTyped := (Profile.rename_hasType_iff
    (ρ := (newDisplay.map.comp τ).comp α)).mpr oldTyped
  have newValueTyped := (Profile.rename_hasType_iff
    (ρ := (newDisplay.map.comp τ).comp α)).mpr newTyped
  simp only [Profile.rename_singleton] at oldValueTyped newValueTyped
  simp only [hmap, htype] at oldOutputs oldCode
  rw [← Profile.rename_comp] at newCode
  obtain ⟨hleft, hright, hpair⟩ := oldOutputs
  have hleft' := lowerIH _ _ _ _ _ _ _ oldValueTyped newValueTyped oldCode newCode hleft
  have hright' := lowerIH _ _ _ _ _ _ _ oldValueTyped newValueTyped oldCode newCode hright
  have hpair' := lowerIH _ _ _ _ _ _ _ oldValueTyped newValueTyped oldCode newCode hpair
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

end Lean4Lean.AnchoredSemantics
