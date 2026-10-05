import Lean4Lean.Theory.Typing.AnchoredSupport
import Lean4Lean.Theory.Typing.AnchoredPiDiagonal

/-! Raw type conversion of an actual function capability. The binary type
witness supplies the actual codomain bridge; only conversion of strictly
smaller-rank output demands is an induction hypothesis. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right oldType newType : VExpr}
    {key : Key n} {output : Atom n}
    {oldTypeProfile newTypeProfile : Profile (n + 1)}
    (henv : env.Ordered)
    (lowerConvert : ∀ Γ l r A B (p oldD newD : Profile n),
      p.HasType newD → TypeRelated env U registry Γ A B newD →
      Related env U registry Γ l r A p oldD → Related env U registry Γ l r B p newD)
    (htyped : (Profile.fn key output).HasType newTypeProfile)
    (hbridge : TypeRelated env U registry Γ oldType newType newTypeProfile)
    (hold : FunctionBehavior env U registry (relations env U registry n)
      Γ left right oldType key output oldTypeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right newType key output newTypeProfile := by
  have sameSupport := FunctionBehavior.retag henv
    (fun _ _ _ _ _ _ _ _ typed _ code term => Related.retag henv typed code term)
    hbridge.left_diagonal htyped hold
  obtain ⟨anchor, A, B, domain, rows, result, hmem, hrow, outputTyped,
    oldDisplay, oldBehavior⟩ := sameSupport
  have hΓ := oldDisplay.leftExposure.generated.baseWF
  have hcore := hbridge Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at hcore
  obtain ⟨binary⟩ := hcore _ hmem
  have hw := htyped.wf_type _ hmem
  have domainTyped : domain.HasType (.sort true) := hw.1
  let newDisplay := PiWitness.right_diagonal henv domainTyped.wf_value
    (fun key result hm => (hw.2 key result hm).2) binary
  refine ⟨anchor, A, B, domain, rows, result, hmem, hrow, outputTyped, newDisplay, ?_⟩
  intro V τ future x y admitted
  change FutureInsertion env U binary.context V τ at future
  change Admitted env U registry V (key.rename (binary.map.comp τ)) x y at admitted
  obtain ⟨C, i, j, oldInsertion, binaryInsertion, hmaps, _, hbodies⟩ :=
    oldDisplay.leftExposure.samePi binary.leftExposure henv
  obtain ⟨W, α, β, proof, extension, hpush⟩ := binaryInsertion.pushout future henv
  obtain ⟨oldW, oldFuture, changed⟩ := oldInsertion.pullFuture henv extension
  have hmap : oldDisplay.map.comp (i.comp β) = (binary.map.comp τ).comp α := by
    rw [← Lift.comp_assoc, hmaps, Lift.comp_assoc, hpush, ← Lift.comp_assoc]
  have hbody : oldDisplay.leftBody.lift' (i.comp β).cons =
      binary.leftBody.lift' (τ.comp α).cons := by
    calc
      _ = (oldDisplay.leftBody.lift' i.cons).lift' β.cons := @lift'_comp i.cons β.cons _
      _ = (binary.leftBody.lift' j.cons).lift' β.cons := congrArg (·.lift' β.cons) hbodies
      _ = binary.leftBody.lift' (j.comp β).cons := (@lift'_comp j.cons β.cons _).symm
      _ = _ := congrArg (fun ρ => binary.leftBody.lift' ρ.cons) hpush
  have htype : (oldDisplay.leftBody.lift' (i.comp β).cons).inst (x.lift' α) =
      ((binary.leftBody.lift' τ.cons).inst x).lift' α := by
    rw [hbody, lift'_inst_hi, ← lift'_comp]
    rfl
  have harg : Admitted env U registry W (key.rename (oldDisplay.map.comp (i.comp β)))
      (x.lift' α) (y.lift' α) := by
    simpa only [← Key.rename_comp, hmap] using proof.admitted henv admitted
  have oldArg := (changed.symm henv).admitted henv harg
  obtain ⟨oldLeft, oldRight, oldCross⟩ :=
    oldBehavior oldW (i.comp β) oldFuture (x.lift' α) (y.lift' α) oldArg
  have outputs := And.intro (changed.term henv oldLeft)
    (And.intro (changed.term henv oldRight) (changed.term henv oldCross))
  have code : TypeRelated env U registry V
      ((binary.leftBody.lift' τ.cons).inst x)
      ((binary.rightBody.lift' τ.cons).inst x)
      (result.rename (binary.map.comp τ)) :=
    (binary.rowBodies key result hrow V τ future x y admitted).2.2
  have liftedCode := proof.code henv code
  have typed := (Profile.rename_hasType_iff (ρ := (binary.map.comp τ).comp α)).mpr outputTyped
  simp only [Profile.rename_singleton] at typed
  simp only [hmap, htype] at outputs
  rw [← Profile.rename_comp] at liftedCode
  obtain ⟨hl, hr, hc⟩ := outputs
  have hl' := lowerConvert _ _ _ _ _ _ _ _ typed liftedCode hl
  have hr' := lowerConvert _ _ _ _ _ _ _ _ typed liftedCode hr
  have hc' := lowerConvert _ _ _ _ _ _ _ _ typed liftedCode hc
  change Related env U registry V
      (.app (left.lift' (binary.map.comp τ)) x) (.app (left.lift' (binary.map.comp τ)) y)
      ((binary.rightBody.lift' τ.cons).inst x)
      (.singleton (output.rename (binary.map.comp τ))) (result.rename (binary.map.comp τ)) ∧
    Related env U registry V
      (.app (right.lift' (binary.map.comp τ)) x) (.app (right.lift' (binary.map.comp τ)) y)
      ((binary.rightBody.lift' τ.cons).inst x)
      (.singleton (output.rename (binary.map.comp τ))) (result.rename (binary.map.comp τ)) ∧
    Related env U registry V
      (.app (left.lift' (binary.map.comp τ)) x) (.app (right.lift' (binary.map.comp τ)) x)
      ((binary.rightBody.lift' τ.cons).inst x)
      (.singleton (output.rename (binary.map.comp τ))) (result.rename (binary.map.comp τ))
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hl'
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hr'
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hc'

end Lean4Lean.AnchoredSemantics
