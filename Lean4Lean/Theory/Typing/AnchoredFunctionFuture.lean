import Lean4Lean.Theory.Typing.AnchoredDiagonal
import Lean4Lean.Theory.Typing.AnchoredFrame
import Lean4Lean.Theory.Typing.AnchoredExposureTransport

/-! Forward transport of actual function behavior. Only the selected left
type exposure is moved to the new world. Duplicating that display supplies
the new diagonal Pi witness, so no paired-exposure transport is assumed.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {key : Key n} {output : Atom n} {typeProfile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (future : FutureInsertion env U Γ Δ ρ)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output typeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (key.rename ρ) (output.rename ρ) (typeProfile.rename ρ) := by
  obtain ⟨anchor, A, B, domain, rows, result, hpi, hrow, htyped, display, behavior⟩ := H
  obtain ⟨Ω, μ, j, extension, hmap, ⟨exposure⟩⟩ :=
    display.leftExposure.future future henv hscoped
  have hbodyMap : display.map.cons.comp j.cons = ρ.cons.comp μ.cons := congrArg Lift.cons hmap
  have hlater (τ : Lift) : display.map.comp (j.comp τ) = ρ.comp (μ.comp τ) := by
    rw [← Lift.comp_assoc, hmap, Lift.comp_assoc]
  let shifted : PiWitness env U registry (relations env U registry n)
      Δ (type.lift' ρ) (type.lift' ρ) (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) (Rows.rename ρ rows) := {
    context := Ω
    map := μ
    leftDomain := display.leftDomain.lift' j
    leftBody := display.leftBody.lift' j.cons
    rightDomain := display.leftDomain.lift' j
    rightBody := display.leftBody.lift' j.cons
    leftExposure := exposure
    rightExposure := exposure
    leftDomainType := display.leftDomainType.weak' henv extension.weakening
    rightDomainType := display.leftDomainType.weak' henv extension.weakening
    leftBodyType := display.leftBodyType.weak' henv extension.weakening.cons
    rightBodyType := display.leftBodyType.weak' henv extension.weakening.cons
    domains := .refl
    bodies := .refl
    prototypeDomainPath := by
      have hp := display.prototypeDomainPath.weak' henv extension.weakening
      rw [← lift'_comp, hmap, lift'_comp] at hp
      exact hp
    prototypeBodyPath := by
      have hp := display.prototypeBodyPath.weak' henv extension.weakening.cons
      rw [← lift'_comp, hbodyMap, lift'_comp] at hp
      exact hp
    domainRelated := by
      simpa only [TypeRelated, ← Profile.rename_comp, hmap] using
        TypeRelated.future henv extension (TypeRelated.left_diagonal display.domainRelated)
    rowDomains := by
      intro newKey newOutput hmem
      obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      obtain ⟨support, hi, hs, hle, hp, hc⟩ := display.rowDomains oldKey oldOutput hsource
      refine ⟨support.rename j, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [Key.rename, ← Profile.rename_comp, hmap] using
          (Profile.rename_hasType_iff (ρ := j)).mpr hi
      · simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := j)).mpr hs
      · change Profile.LE _ _
        simpa only [← Profile.rename_comp, hmap] using (Profile.rename_le_iff (ρ := j)).mpr hle
      · simpa only [Key.rename, ← lift'_comp, hmap] using hp.weak' henv extension.weakening
      · simpa only [TypeRelated, Key.rename, ← lift'_comp, hmap] using
          TypeRelated.future henv extension hc
    rowBodies := by
      intro newKey newOutput hmem Ξ τ later x y admitted
      obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      have harg : Admitted env U registry Ξ (oldKey.rename (display.map.comp (j.comp τ))) x y := by
        simpa only [Admitted, ← Key.rename_comp, hlater] using admitted
      have h := (display.rowBodies oldKey oldOutput hsource Ξ (j.comp τ)
        (extension.comp later henv) x y harg).1
      have hd := TypeRelated.left_diagonal h
      simpa only [TypeRelated, ← lift'_comp, show j.cons.comp τ.cons = (j.comp τ).cons from rfl,
        ← Profile.rename_comp, hlater] using And.intro h (And.intro h hd) }
  refine ⟨Admitted.future henv future anchor,
    A.lift' ρ, B.lift' ρ.cons, domain.rename ρ, Rows.rename ρ rows, result.rename ρ,
    List.mem_map.mpr ⟨.pi A B domain rows, hpi, rfl⟩,
    List.mem_map.mpr ⟨(key, result), hrow, rfl⟩, ?_, shifted, ?_⟩
  · simpa only [Profile.rename_singleton] using (Profile.rename_hasType_iff (ρ := ρ)).mpr htyped
  · intro Ξ τ later x y admitted
    have harg : Admitted env U registry Ξ (key.rename (display.map.comp (j.comp τ))) x y := by
      simpa only [Admitted, shifted, ← Key.rename_comp, hlater] using admitted
    have h := behavior Ξ (j.comp τ) (extension.comp later henv) x y harg
    simpa only [shifted, ← lift'_comp, show j.cons.comp τ.cons = (j.comp τ).cons from rfl,
      ← Atom.rename_comp, ← Profile.rename_comp, hlater] using h

end Lean4Lean.AnchoredSemantics
