import Lean4Lean.Theory.Typing.AnchoredCodeExtraction
import Lean4Lean.Theory.Typing.AnchoredMinimalSupport
import Lean4Lean.Theory.Typing.NativeCaptureAbstraction

/-! Recover a function key's supported raw-domain alignment from its actual
semantic evidence at a literal Pi type. This uses trace shape, not typing
uniqueness or retraction of a private semantic component. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem literalPi_trace
    {registry : CanonicalHead.Registry} {A B result : VExpr} {added : List VExpr}
    (h : CanonicalDataHead.Trace registry (.forallE A B) added result) :
    added = [] ∧ result = .forallE A B := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | next step _ => simp only [CanonicalDataHead.step_pi] at step; contradiction

private theorem Exposure.literalPi_domain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {A B C D : VExpr}
    (E : Exposure env U registry Γ (.forallE A B) Δ ρ (.forallE C D)) :
    C = A.lift' ρ := by
  have ht := literalPi_trace E.trace
  have hm : E.postMap = ρ := by
    simpa only [ht.1, List.length_nil, Lift.skipN, Lift.refl_comp] using E.map_eq
  have he := E.result_eq
  rw [ht.2, hm] at he
  exact (VExpr.forallE.inj he).1.symm

private theorem exposureInsertion
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

/-- A function demand at a literal Pi type supplies a base-context guard for
its frozen key domain. The finite support is selected from the original type
cover before any private display context is consulted. -/
theorem Related.fn_domain_alignment
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right A B : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right (.forallE A B)
      (Profile.fn key output) typeProfile) :
    ∃ support : Profile n, key.input.HasType support ∧ support.HasType (.sort true) ∧
      TypeConversion env U Γ key.domain A ∧
      TypeRelated env U registry Γ key.domain A support := by
  have typed : (Profile.fn key output).HasType typeProfile := by
    have hs := H (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
    simp only [lift'_refl, Profile.rename_refl] at hs
    rcases hs with hempty | ⟨Δ, ρ, _, ht, _, _⟩
    · cases hempty
    · exact Profile.rename_hasType_iff.mp ht
  have code := H.typeCode henv hscoped hΓ (by intro he; cases he)
  obtain ⟨prototypeA, prototypeB, domain, rows, result,
    hpi, _, _, inputTyped, hrow, _⟩ := typed.fn_inv (List.mem_singleton_self _)
  obtain ⟨support, hsupport⟩ := Basis.exists inputTyped
  have minimal := Basis.minimal hsupport
  obtain ⟨supportTyped, supportBound⟩ := Basis.valid hsupport
  have hc := code Γ .refl (.refl hΓ) (.pi prototypeA prototypeB domain rows)
    (by simpa only [Profile.rename_refl] using hpi)
  simp only [lift'_refl] at hc
  obtain ⟨display⟩ := hc
  have hdomain := display.leftExposure.literalPi_domain
  have insertion := exposureInsertion henv display.leftExposure
  obtain ⟨localSupport, localTyped, _, _, raw, bridge⟩ := display.rowDomains key result hrow
  have focused := TypeRelated.focusMinimal henv (minimal.rename display.map)
    (Profile.rename_le_iff.mpr supportBound) (TypeRelated.left_diagonal display.domainRelated)
  have aligned := (focused.composeMinimal henv (minimal.rename display.map)
    localTyped (TypeRelated.symm henv localTyped.wf_type bridge)).symm henv
      ((Profile.rename_hasType_iff.mpr supportTyped).wf_type)
  change TypeRelated env U registry display.context (key.domain.lift' display.map)
    display.leftDomain (support.rename display.map) at aligned
  rw [hdomain] at aligned raw
  have baseCode := insertion.codeBack henv hscoped aligned
  have basePath := insertion.pathBack henv raw
  exact ⟨support, supportTyped, minimal.formation, basePath, baseCode⟩

end Lean4Lean.AnchoredSemantics
