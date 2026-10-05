import Lean4Lean.Theory.Typing.AnchoredExposureCopy
import Lean4Lean.Theory.Typing.AnchoredProofDrop
import Lean4Lean.Theory.Typing.AnchoredFunctionDisplayReplay

/-! Query a new function proof at an already retained actual type display.
Fresh copies of that display's proof slots are contracted to the retained
ones. The function terms and arguments may use any other variables in the
current world, including an independently generated native proof prefix. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.atEarlierDisplay
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} {type A B left right : VExpr}
    {domain result : Profile n} {rows : List (Key n × Profile n)}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)} {ρ : Lift}
    (original : PiWitness env U registry (relations env U registry n)
      Γ type type A B domain rows)
    (row : (key, result) ∈ rows) (typed : (Profile.singleton output).HasType result)
    (future : FutureInsertion env U original.context Δ ρ)
    {x y : VExpr}
    (admitted : Admitted env U registry Δ (key.rename (original.map.comp ρ)) x y)
    (hold : FunctionBehavior env U registry (relations env U registry n) Δ
      left right (type.lift' (original.map.comp ρ))
      (key.rename (original.map.comp ρ)) (output.rename (original.map.comp ρ)) support) :
    Related env U registry Δ (.app left x) (.app left y)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) ∧
    Related env U registry Δ (.app right x) (.app right y)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) ∧
    Related env U registry Δ (.app left x) (.app right x)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) := by
  obtain ⟨_, newA, newB, newDomain, newRows, newResult, _, newRow, newTyped,
    display, behavior⟩ := hold
  obtain ⟨copy, copyMap, addedEq, _, headCopy⟩ :=
    original.leftExposure.piCopyRetraction henv hscoped future display.leftExposure
  have copyInsertion : ProofInsertion env U Δ
      (renameAdded (original.map.comp ρ) original.leftExposure.added ++ Δ) copy.liftMap := by
    rw [copyMap]
    simpa only [addedEq, renameAdded_length] using display.leftExposure.generated
  have post : ProofInsertion env U
      (renameAdded (original.map.comp ρ) original.leftExposure.added ++ Δ)
      display.leftExposure.postContext display.leftExposure.postMap := by
    simpa only [addedEq] using display.leftExposure.post
  have displayMap : copy.liftMap.comp display.leftExposure.postMap = display.map := by
    rw [copyMap]
    simpa only [addedEq, renameAdded_length] using display.leftExposure.map_eq
  obtain ⟨extended⟩ := copy.extendProof copyInsertion post henv
  obtain ⟨oldWorld, oldFuture, changed⟩ :=
    display.leftExposure.terminal.pushFuture henv extended.oldFuture
  have maps : display.map.comp extended.oldMap =
      extended.smallMap.comp extended.drop.liftMap := by
    exact (congrArg (·.comp extended.oldMap) displayMap.symm).trans extended.square
  have bodyCopy : display.leftBody.subst extended.readback.lift =
      (original.leftBody.lift' ρ.cons).lift' extended.smallMap.cons := by
    have h := extended.commute display.leftExposure.result
    rw [display.leftExposure.result_eq, headCopy] at h
    exact (VExpr.forallE.inj h).2
  have body (argument : VExpr) :
      (((display.leftBody.lift' extended.oldMap.cons).inst
        ((argument.lift' extended.smallMap).lift' extended.drop.liftMap)).subst
          extended.drop.retract) =
      (((original.leftBody.lift' ρ.cons).inst argument).lift' extended.smallMap) := by
    rw [subst_inst, subst_lift', ← Subst.lift_l_lift, extended.restrict,
      bodyCopy, extended.drop.leftInv, lift'_inst_hi]
  have incoming := (admitted.future henv extended.smallFrame.toFuture).future
    henv extended.proofSection.toFuture
  have newAdmission : Admitted env U registry extended.context
      ((key.rename (original.map.comp ρ)).rename (display.map.comp extended.oldMap))
      ((x.lift' extended.smallMap).lift' extended.drop.liftMap)
      ((y.lift' extended.smallMap).lift' extended.drop.liftMap) := by
    simpa only [← Key.rename_comp, maps, Lift.comp_assoc] using incoming
  obtain ⟨first, second, cross⟩ := behavior oldWorld extended.oldMap oldFuture
    ((x.lift' extended.smallMap).lift' extended.drop.liftMap)
    ((y.lift' extended.smallMap).lift' extended.drop.liftMap)
    (changed.admitted henv newAdmission)
  have first := (changed.symm henv).term henv first
  have second := (changed.symm henv).term henv second
  have cross := (changed.symm henv).term henv cross
  have outputCode := TypeRelated.left_diagonal
    (original.rowBodies key result row Δ ρ future x y admitted).1
  have outputTyped := (Profile.rename_hasType_iff (ρ := original.map.comp ρ)).mpr typed
  simp only [Profile.rename_singleton] at outputTyped
  have finish {a b u v : VExpr}
      (related : Related env U registry extended.context
        (.app (a.lift' (display.map.comp extended.oldMap))
          ((u.lift' extended.smallMap).lift' extended.drop.liftMap))
        (.app (b.lift' (display.map.comp extended.oldMap))
          ((v.lift' extended.smallMap).lift' extended.drop.liftMap))
        ((display.leftBody.lift' extended.oldMap.cons).inst
          ((x.lift' extended.smallMap).lift' extended.drop.liftMap))
        (.singleton ((output.rename (original.map.comp ρ)).rename
          (display.map.comp extended.oldMap)))
        (newResult.rename (display.map.comp extended.oldMap))) :
      Related env U registry Δ (.app a u) (.app b v)
        ((original.leftBody.lift' ρ.cons).inst x)
        (.singleton (output.rename (original.map.comp ρ)))
        (result.rename (original.map.comp ρ)) := by
    have guarded : Related env U registry extended.context
        (.app (a.lift' (display.map.comp extended.oldMap))
          ((u.lift' extended.smallMap).lift' extended.drop.liftMap))
        (.app (b.lift' (display.map.comp extended.oldMap))
          ((v.lift' extended.smallMap).lift' extended.drop.liftMap))
        ((display.leftBody.lift' extended.oldMap.cons).inst
          ((x.lift' extended.smallMap).lift' extended.drop.liftMap))
        ((Profile.singleton ((output.rename (original.map.comp ρ)).rename extended.smallMap)).rename
          extended.drop.liftMap)
        ((newResult.rename extended.smallMap).rename extended.drop.liftMap) := by
      simpa only [maps, Profile.rename_singleton, Atom.rename_comp, Profile.rename_comp]
        using related
    have dropped := Related.drop henv hscoped extended.drop extended.proofSection guarded
    have applications (a u : VExpr) :
        (VExpr.app (a.lift' (display.map.comp extended.oldMap))
          ((u.lift' extended.smallMap).lift' extended.drop.liftMap)).subst extended.drop.retract =
          (VExpr.app a u).lift' extended.smallMap := by
      rw [maps, lift'_comp]
      simp only [subst, extended.drop.leftInv, lift']
    have base : Related env U registry Δ (.app a u) (.app b v)
        ((original.leftBody.lift' ρ.cons).inst x)
        (.singleton (output.rename (original.map.comp ρ))) newResult := by
      apply Related.absorb henv extended.smallFrame
      simpa only [applications, body, Profile.rename_singleton] using dropped
    exact Related.retag henv outputTyped outputCode base
  exact ⟨finish first, finish second, finish cross⟩

theorem Related.atEarlierDisplay
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} {type A B left right : VExpr}
    {domain result : Profile n} {rows : List (Key n × Profile n)}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)} {ρ : Lift}
    (original : PiWitness env U registry (relations env U registry n)
      Γ type type A B domain rows)
    (row : (key, result) ∈ rows) (typed : (Profile.singleton output).HasType result)
    (future : FutureInsertion env U original.context Δ ρ)
    {x y : VExpr}
    (admitted : Admitted env U registry Δ (key.rename (original.map.comp ρ)) x y)
    (related : Related env U registry Δ left right (type.lift' (original.map.comp ρ))
      (.fn (key.rename (original.map.comp ρ)) (output.rename (original.map.comp ρ))) support) :
    Related env U registry Δ (.app left x) (.app left y)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) ∧
    Related env U registry Δ (.app right x) (.app right y)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) ∧
    Related env U registry Δ (.app left x) (.app right x)
      ((original.leftBody.lift' ρ.cons).inst x)
      (.singleton (output.rename (original.map.comp ρ))) (result.rename (original.map.comp ρ)) :=
  FunctionBehavior.atEarlierDisplay henv hscoped original row typed future admitted
    (related.functionBehavior henv hscoped (future.targetWF henv))

end Lean4Lean.AnchoredSemantics
