import Lean4Lean.Theory.Typing.AnchoredSortComposition

/-! Transitivity of code capabilities at one fixed finite profile. Pi
composition retains the first row-domain bridges and composes the actual
codomain cross links at the strictly smaller rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem lift_cons_comp (e : VExpr) (ρ τ : Lift) :
    e.lift' (ρ.comp τ).cons = (e.lift' ρ.cons).lift' τ.cons :=
  @VExpr.lift'_comp ρ.cons τ.cons e

/-- No well-formedness or minimality assumption is needed when both actual
Pi capabilities already interpret exactly the same domain and row supports. -/
theorem PiWitness.trans
    {n : Nat} {Γ : List VExpr} {left middle right A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered)
    (lowerTrans : ∀ Γ X Y Z (profile : Profile n),
      TypeRelated env U registry Γ X Y profile →
      TypeRelated env U registry Γ Y Z profile →
      TypeRelated env U registry Γ X Z profile)
    (first : PiWitness env U registry (relations env U registry n)
      Γ left middle A B domain rows)
    (second : PiWitness env U registry (relations env U registry n)
      Γ middle right A B domain rows) :
    Nonempty (PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) := by
  obtain ⟨Ω, i, j, hi, hj, hmaps, hdomains, hbodies⟩ :=
    first.rightExposure.samePi second.leftExposure henv
  have leftType := hi.isType henv first.leftDomainType
  have middleType := hi.isType henv first.rightDomainType
  have dom₁ := hi.path henv first.domains
  have dom₂ := hj.path henv second.domains
  rw [← hdomains] at dom₂
  have body₁ := hi.pathUnderBinder henv first.leftDomainType first.bodies
  have body₂ := hj.pathUnderBinder henv second.leftDomainType second.bodies
  rw [← hdomains, ← hbodies] at body₂
  obtain ⟨u, hu⟩ := leftType
  obtain ⟨v, hv⟩ := middleType
  have paths := TypeConversion.composePi henv (hi.targetWF henv (first.leftExposure.targetWF henv)) hu hv
    dom₁ dom₂ body₁ body₂
  have code₁ := hi.code henv first.domainRelated
  have code₂ := hj.code henv second.domainRelated
  simp only [← Profile.rename_comp] at code₁ code₂
  rw [← hmaps, ← hdomains] at code₂
  have domainCode := lowerTrans _ _ _ _ _ code₁ code₂
  refine ⟨{
    context := Ω
    map := first.map.comp i
    leftDomain := first.leftDomain.lift' i
    leftBody := first.leftBody.lift' i.cons
    rightDomain := second.rightDomain.lift' j
    rightBody := second.rightBody.lift' j.cons
    leftExposure := first.leftExposure.postMixed henv hi
    rightExposure := ?_
    leftDomainType := ⟨u, hu⟩
    rightDomainType := hj.isType henv second.rightDomainType
    leftBodyType := hi.isTypeUnderBinder henv first.leftDomainType first.leftBodyType
    rightBodyType := hj.isTypeUnderBinder henv second.rightDomainType second.rightBodyType
    domains := paths.1
    bodies := paths.2
    prototypeDomainPath := ?_
    prototypeBodyPath := ?_
    domainRelated := domainCode
    rowDomains := ?_
    rowBodies := ?_ }⟩
  · rw [hmaps]
    exact second.rightExposure.postMixed henv hj
  · simpa only [lift'_comp] using hi.path henv first.prototypeDomainPath
  · simpa only [lift_cons_comp] using
      hi.pathUnderBinder henv first.leftDomainType first.prototypeBodyPath
  · intro k r hrow
    obtain ⟨s, hs, hsort, hle, path, code⟩ :=
      first.rowDomains k r hrow
    refine ⟨s.rename i, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Key.rename, Profile.rename_comp] using
        (Profile.rename_hasType_iff (ρ := i)).mpr hs
    · simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := i)).mpr hsort
    · change Profile.LE (s.rename i) (domain.rename (first.map.comp i))
      simpa only [Profile.rename_comp] using (Profile.rename_le_iff (ρ := i)).mpr hle
    · simpa only [lift'_comp] using hi.path henv path
    · simpa only [TypeRelated, lift'_comp] using hi.code henv code
  · intro k r hrow Δ ρ future x y admitted
    have hmap : first.map.comp (i.comp ρ) = second.map.comp (j.comp ρ) := by
      rw [← Lift.comp_assoc, hmaps, Lift.comp_assoc]
    have arg₁ : Admitted env U registry Δ (k.rename (first.map.comp (i.comp ρ))) x y := by
      simpa only [Admitted, Lift.comp_assoc] using admitted
    have arg₂ : Admitted env U registry Δ (k.rename (second.map.comp (j.comp ρ))) x y := by
      rw [← hmap]
      exact arg₁
    have out₁ := first.rowBodies_mixed henv hi hrow future x y arg₁
    have out₂ := second.rowBodies_mixed henv hj hrow future x y arg₂
    have middleBody : first.rightBody.lift' (i.comp ρ).cons =
        second.leftBody.lift' (j.comp ρ).cons := by
      simpa only [lift_cons_comp] using congrArg (·.lift' ρ.cons) hbodies
    simp only [← hmap, ← middleBody] at out₂
    have cross := lowerTrans _ _ _ _ _ out₁.2.2 out₂.2.2
    simpa only [TypeRelated, lift_cons_comp, Lift.comp_assoc] using
      And.intro out₁.1 (And.intro out₂.2.1 cross)

end Lean4Lean.AnchoredSemantics
