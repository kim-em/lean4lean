import Lean4Lean.Theory.Typing.AnchoredEarlierFunctionDisplay
import Lean4Lean.Theory.Typing.AnchoredFunctionIntroduction
import Lean4Lean.Theory.Typing.AnchoredLiteralPi
import Lean4Lean.Theory.Typing.AnchoredSymmetry

/-! A comparison at the frozen argument determines the cross-function clause.
The two original self comparisons supply variation in admitted arguments; the
actual retained Pi row supplies its dependent result-type conversion. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem anchor_argument
    (h : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key key.anchor x := by
  obtain ⟨anchor, _, support, typed, formed, code, first, _⟩ := h
  exact ⟨anchor.hasType.1, anchor, support, typed, formed, code,
    Related.left_diagonal first, first⟩

/-- The original self witnesses may have different supports. Their behavior
is replayed at this actual display, so no equality of private displays or of
their result supports is assumed. -/
theorem Related.functionAtAnchor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right A B prototypeDomain prototypeBody : VExpr}
    {key : Key n} {output : Atom n} {domain result : Profile n}
    {rows : List (Key n × Profile n)}
    {support leftSupport rightSupport : Profile (n + 1)}
    (display : PiWitness env U registry (relations env U registry n)
      Γ (.forallE A B) (.forallE A B) prototypeDomain prototypeBody domain rows)
    (member : (AtomData.pi prototypeDomain prototypeBody domain rows : Atom (n + 1)) ∈ support.atoms)
    (row : (key, result) ∈ rows) (outputTyped : (Profile.singleton output).HasType result)
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry Γ (.forallE A B) (.forallE A B) support)
    (leftSelf : Related env U registry Γ left left (.forallE A B) (.fn key output) leftSupport)
    (rightSelf : Related env U registry Γ right right (.forallE A B) (.fn key output) rightSupport)
    (anchor : Related env U registry Γ (.app left key.anchor) (.app right key.anchor)
      (B.inst key.anchor) (.singleton output) result) :
    Related env U registry Γ left right (.forallE A B) (.fn key output) support := by
  apply Related.function henv hscoped typed code
  refine ⟨(leftSelf.functionBehavior henv hscoped hΓ).1,
    prototypeDomain, prototypeBody, domain, rows, result, member, row, outputTyped, display, ?_⟩
  intro Δ ρ future x y admitted
  let ν := display.map.comp ρ
  have insertion := display.leftExposure.insertion henv
  have leftMoved := (insertion.term henv leftSelf).future henv future
  have rightMoved := (insertion.term henv rightSelf).future henv future
  simp only [← lift'_comp, ← Profile.rename_comp, Profile.fn, Profile.rename_singleton,
    Atom.rename_fn, ← Key.rename_comp, ← Atom.rename_comp] at leftMoved rightMoved
  have leftPair := leftMoved.atEarlierDisplay henv hscoped display row outputTyped future admitted
  have rightPair := rightMoved.atEarlierDisplay henv hscoped display row outputTyped future admitted
  have anchored := anchor_argument admitted
  have leftAnchor := leftMoved.atEarlierDisplay henv hscoped display row outputTyped future anchored
  have rightAnchor := rightMoved.atEarlierDisplay henv hscoped display row outputTyped future anchored
  have cross := (insertion.term henv anchor).future henv future
  simp only [← lift'_comp, ← Profile.rename_comp] at cross
  have body := display.leftExposure.literalPi_components.2
  have bodyAnchor : (display.leftBody.lift' ρ.cons).inst (key.anchor.lift' ν) =
      (B.inst key.anchor).lift' ν := by
    rw [body, ← lift'_comp]
    change (B.lift' ν.cons).inst (key.anchor.lift' ν) = _
    rw [lift'_inst_hi]
  have cross' : Related env U registry Δ
      (.app (left.lift' ν) (key.anchor.lift' ν))
      (.app (right.lift' ν) (key.anchor.lift' ν))
      ((display.leftBody.lift' ρ.cons).inst (key.anchor.lift' ν))
      (.singleton (output.rename ν)) (result.rename ν) := by
    simpa only [bodyAnchor, lift', Profile.rename_singleton, ν] using cross
  have atAnchor := Related.trans henv hscoped (Related.symm henv leftAnchor.1)
    (cross'.trans henv hscoped rightAnchor.1)
  have resultCode := (display.rowBodies key result row Δ ρ future _ _ anchored).1
  have typed' : (Profile.singleton (output.rename ν)).HasType (result.rename ν) := by
    simpa only [Profile.rename_singleton] using
      (Profile.rename_hasType_iff (ρ := ν)).mpr outputTyped
  exact ⟨leftPair.1, rightPair.1, Related.convert henv typed' resultCode atAnchor⟩

end Lean4Lean.AnchoredSemantics
