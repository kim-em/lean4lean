import Lean4Lean.Theory.Typing.AnchoredSupport

/-! Composition of actual function capabilities at a fixed key and atomic
output. The second display and type support are retained. Only composition
of strictly smaller-rank output relations is an induction hypothesis. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left middle right type : VExpr} {key : Key n} {output : Atom n}
    {firstTypeProfile secondTypeProfile : Profile (n + 1)}
    (henv : env.Ordered)
    (lowerTrans : ∀ Γ l m r A (p d₁ d₂ : Profile n),
      Related env U registry Γ l m A p d₁ → Related env U registry Γ m r A p d₂ →
      Related env U registry Γ l r A p d₂)
    (first : FunctionBehavior env U registry (relations env U registry n)
      Γ left middle type key output firstTypeProfile)
    (second : FunctionBehavior env U registry (relations env U registry n)
      Γ middle right type key output secondTypeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output secondTypeProfile := by
  obtain ⟨_, firstA, firstB, firstDom, firstRows, firstResult, _, firstRow, _,
    firstDisplay, firstBehavior⟩ := first
  obtain ⟨seed, secondA, secondB, secondDom, secondRows, secondResult, secondMem,
    secondRow, secondTyped, secondDisplay, secondBehavior⟩ := second
  refine ⟨seed, secondA, secondB, secondDom, secondRows, secondResult, secondMem,
    secondRow, secondTyped, secondDisplay, ?_⟩
  intro V τ future x y admitted
  obtain ⟨C, i, j, firstInsertion, secondInsertion, hmaps, _, hbodies⟩ :=
    firstDisplay.leftExposure.samePi secondDisplay.leftExposure henv
  obtain ⟨W, α, β, proof, extension, hpush⟩ := secondInsertion.pushout future henv
  obtain ⟨firstW, firstFuture, changed⟩ := firstInsertion.pullFuture henv extension
  have hmap : firstDisplay.map.comp (i.comp β) = (secondDisplay.map.comp τ).comp α := by
    rw [← Lift.comp_assoc, hmaps, Lift.comp_assoc, hpush, ← Lift.comp_assoc]
  have hbody : firstDisplay.leftBody.lift' (i.comp β).cons =
      secondDisplay.leftBody.lift' (τ.comp α).cons := by
    calc
      _ = (firstDisplay.leftBody.lift' i.cons).lift' β.cons := @lift'_comp i.cons β.cons _
      _ = (secondDisplay.leftBody.lift' j.cons).lift' β.cons := congrArg (·.lift' β.cons) hbodies
      _ = secondDisplay.leftBody.lift' (j.comp β).cons := (@lift'_comp j.cons β.cons _).symm
      _ = _ := congrArg (fun ρ => secondDisplay.leftBody.lift' ρ.cons) hpush
  have htype : (firstDisplay.leftBody.lift' (i.comp β).cons).inst (x.lift' α) =
      ((secondDisplay.leftBody.lift' τ.cons).inst x).lift' α := by
    rw [hbody, lift'_inst_hi, ← lift'_comp]
    rfl
  have harg : Admitted env U registry W (key.rename (firstDisplay.map.comp (i.comp β)))
      (x.lift' α) (y.lift' α) := by
    simpa only [← Key.rename_comp, hmap] using proof.admitted henv admitted
  have firstArg := (changed.symm henv).admitted henv harg
  obtain ⟨firstLeft, firstRight, firstCross⟩ :=
    firstBehavior firstW (i.comp β) firstFuture (x.lift' α) (y.lift' α) firstArg
  have firstOutputs := And.intro (changed.term henv firstLeft)
    (And.intro (changed.term henv firstRight) (changed.term henv firstCross))
  have secondOutputs := secondBehavior V τ future x y admitted
  have secondCode := TypeRelated.left_diagonal
    (secondDisplay.rowBodies key secondResult secondRow V τ future x y admitted).1
  have liftedCode := proof.code henv secondCode
  have liftedCross := proof.term henv secondOutputs.2.2
  have typed := (Profile.rename_hasType_iff
    (ρ := (secondDisplay.map.comp τ).comp α)).mpr secondTyped
  simp only [Profile.rename_singleton] at typed
  simp only [hmap, htype] at firstOutputs
  simp only [← Profile.rename_comp] at liftedCode
  have leftSelf := Related.retag henv typed liftedCode firstOutputs.1
  have secondCross : Related env U registry W
      (.app (middle.lift' ((secondDisplay.map.comp τ).comp α)) (x.lift' α))
      (.app (right.lift' ((secondDisplay.map.comp τ).comp α)) (x.lift' α))
      (((secondDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      (.singleton (output.rename ((secondDisplay.map.comp τ).comp α)))
      (secondResult.rename ((secondDisplay.map.comp τ).comp α)) := by
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using liftedCross
  have cross := lowerTrans _ _ _ _ _ _ _ _ firstOutputs.2.2 secondCross
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using leftSelf
  constructor
  · exact secondOutputs.2.1
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using cross

end Lean4Lean.AnchoredSemantics
