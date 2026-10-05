import Lean4Lean.Theory.Typing.AnchoredKeyAdapterInterpretation

/-! The function step for hereditary endpoint-supported adapters. Its two
interpretation hypotheses are at strictly smaller rank; the closed rank
induction is in AnchoredAdapterInterpretation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem exposureInsertion {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

theorem FunctionBehavior.adapt
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {oldTypeProfile newTypeProfile : Profile (n + 1)} {newKey : Key n} {newOutput : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lowerAtom : ∀ {Δ : List VExpr} {a b : Atom n},
      AtomAdapter env U registry Δ a b → ∀ {l r A : VExpr} {old new : Profile n},
      (Profile.singleton b).HasType new → TypeRelated env U registry Δ A A new →
      Related env U registry Δ l r A (.singleton a) old →
      Related env U registry Δ l r A (.singleton b) new)
    (lowerProfile : ∀ {Δ : List VExpr} {p q : Profile n},
      ProfileAdapter env U registry Δ p q → ∀ {l r A : VExpr} {old new : Profile n},
      q.HasType new → TypeRelated env U registry Δ A A new →
      Related env U registry Δ l r A p old → Related env U registry Δ l r A q new)
    (keys : KeyProgram env U registry Γ key newKey)
    (result : AtomAdapter env U registry Γ output newOutput)
    (hnew : TypeRelated env U registry Γ type type newTypeProfile)
    (htyped : (Profile.fn newKey newOutput).HasType newTypeProfile)
    (hold : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output oldTypeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type newKey newOutput newTypeProfile := by
  obtain ⟨oldSeed, hold⟩ := hold
  obtain ⟨oldA, oldB, oldDom, oldRows, oldResult, _, oldRow, oldTyped,
    oldDisplay, oldBehavior⟩ := hold
  have hΓ := oldDisplay.leftExposure.generated.baseWF
  have newSeed := keys.forward henv hscoped hΓ oldSeed
  refine ⟨newSeed, ?_⟩
  obtain ⟨newA, newB, newDom, newRows, newResult, newMem, _, _, _, newRow, newTyped⟩ :=
    htyped.fn_inv (List.mem_singleton_self _)
  change Profile n at newDom newResult
  change List (Key n × Profile n) at newRows
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
  have full := (exposureInsertion henv oldDisplay.leftExposure).comp oldInsertion
  have newArg : Admitted env U registry W
      (newKey.rename (oldDisplay.map.comp (i.comp β))) (x.lift' α) (y.lift' α) := by
    simpa only [← Key.rename_comp, hmap] using
      proof.admitted henv admitted
  have keys' : KeyProgram env U registry W
      (key.rename (oldDisplay.map.comp (i.comp β)))
      (newKey.rename (oldDisplay.map.comp (i.comp β))) := by
    simpa only [← Key.rename_comp, Lift.comp_assoc] using (keys.mixed henv full).future henv extension
  have seed' : Admitted env U registry W (key.rename (oldDisplay.map.comp (i.comp β)))
      (key.anchor.lift' (oldDisplay.map.comp (i.comp β)))
      (key.anchor.lift' (oldDisplay.map.comp (i.comp β))) := by
    simpa only [← Key.rename_comp, ← lift'_comp, Lift.comp_assoc] using
      Admitted.future henv extension (full.admitted henv oldSeed)
  have harg := keys'.pullWith henv hscoped (extension.targetWF henv) lowerProfile seed' newArg
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
      (newDisplay.rowBodies newKey newResult newRow V τ future x y admitted).1)
  have newValueTyped := (Profile.rename_hasType_iff
    (ρ := (newDisplay.map.comp τ).comp α)).mpr newTyped
  simp only [Profile.rename_singleton] at newValueTyped
  simp only [hmap, htype] at oldOutputs
  rw [← Profile.rename_comp] at newCode
  obtain ⟨hleft, hright, hpair⟩ := oldOutputs
  have result' : AtomAdapter env U registry W
      (output.rename (oldDisplay.map.comp (i.comp β)))
      (newOutput.rename (oldDisplay.map.comp (i.comp β))) := by
    simpa only [← Atom.rename_comp, Lift.comp_assoc] using (result.mixed henv full).future henv extension
  rw [hmap] at result'
  have hleft' := lowerAtom result' newValueTyped newCode hleft
  have hright' := lowerAtom result' newValueTyped newCode hright
  have hpair' := lowerAtom result' newValueTyped newCode hpair
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
