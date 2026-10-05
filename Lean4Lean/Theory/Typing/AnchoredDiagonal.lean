import Lean4Lean.Theory.Typing.AnchoredSemantics
import Lean4Lean.Theory.Typing.AnchoredDataDiagonal

/-! Left diagonals for the concrete rank-recursive anchored relations.
The proofs retain the original exposures, proof insertions and function rows.
Only the already defined lower rank is used to make codomain and term
relations reflexive at their left endpoint. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem SortRelated.left_diagonal
    (H : SortRelated env U registry Γ left right relevant) :
    SortRelated env U registry Γ left left relevant := by
  obtain ⟨Δ, ρ, u, _, hl, _, _, hu⟩ := H
  exact ⟨Δ, ρ, u, u, hl, hl, rfl, hu⟩

private theorem left_diagonals (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (n : Nat) :
    (∀ Γ left right profile,
      (relations env U registry n).code Γ left right profile →
      (relations env U registry n).code Γ left left profile) ∧
    (∀ Γ left right type value typeProfile,
      (relations env U registry n).term Γ left right type value typeProfile →
      (relations env U registry n).term Γ left left type value typeProfile) := by
  induction n with
  | zero =>
    constructor
    · intro Γ left right profile h Δ ρ future relevant hr
      exact (h Δ ρ future relevant hr).left_diagonal
    · intro Γ left right type value typeProfile h requested hrequested Ω τ future
      rcases h requested hrequested Ω τ future with hempty | ⟨Δ, ρ, insertion, typed, typeRelated, termRelated⟩
      · exact .inl hempty
      · exact .inr ⟨Δ, ρ, insertion, typed, typeRelated,
          fun Ξ γ later relevant hr => (termRelated Ξ γ later relevant hr).left_diagonal⟩
  | succ n ih =>
    have codeAtomDiagonal : ∀ Γ left right atom,
        CodeAtom env U registry (relations env U registry n) Γ left right atom →
        CodeAtom env U registry (relations env U registry n) Γ left left atom := by
      intro Γ left right atom h
      cases atom with
      | sort relevant => exact SortRelated.left_diagonal h
      | fn | ctor | record => exact False.elim h
      | family demand =>
        obtain ⟨witness⟩ := h
        exact ⟨witness.left_diagonal ih.2⟩
      | pad atom => exact ih.1 _ _ _ _ h
      | pi A B domain rows =>
        obtain ⟨display⟩ := h
        refine ⟨{
          context := display.context
          map := display.map
          leftDomain := display.leftDomain
          leftBody := display.leftBody
          rightDomain := display.leftDomain
          rightBody := display.leftBody
          leftExposure := display.leftExposure
          rightExposure := display.leftExposure
          leftDomainType := display.leftDomainType
          rightDomainType := display.leftDomainType
          leftBodyType := display.leftBodyType
          rightBodyType := display.leftBodyType
          domains := .refl
          bodies := .refl
          prototypeDomainPath := display.prototypeDomainPath
          prototypeBodyPath := display.prototypeBodyPath
          domainRelated := ih.1 _ _ _ _ display.domainRelated
          rowDomains := display.rowDomains
          rowBodies := ?_ }⟩
        intro key output hrow Δ ρ future x y admitted
        have h := (display.rowBodies key output hrow Δ ρ future x y admitted).1
        exact ⟨h, h, ih.1 _ _ _ _ h⟩
    constructor
    · intro Γ left right profile h Δ ρ future atom ha
      exact codeAtomDiagonal Δ _ _ atom (h Δ ρ future atom ha)
    · intro Γ left right type value typeProfile h requested hrequested Ω τ future
      rcases h requested hrequested Ω τ future with hempty | ⟨Δ, ρ, insertion, typed, typeRelated, termRelated⟩
      · exact .inl hempty
      · refine .inr ⟨Δ, ρ, insertion, typed, typeRelated, ?_⟩
        intro atom ha
        have h := termRelated atom ha
        cases atom with
        | sort relevant =>
          intro Δ ρ future a ha
          exact codeAtomDiagonal _ _ _ a (h Δ ρ future a ha)
        | pi A B domain rows =>
          intro Δ ρ future a ha
          exact codeAtomDiagonal _ _ _ a (h Δ ρ future a ha)
        | family demand =>
          intro Δ ρ future a ha
          exact codeAtomDiagonal _ _ _ a (h Δ ρ future a ha)
        | ctor demand =>
          exact RankedData.ConstructorRelation.left_diagonal ih.2 h
        | record demand =>
          exact RankedData.RecordRelation.left_diagonal ih.2 h
        | pad atom => exact ih.2 _ _ _ _ _ _ h
        | fn key output =>
          obtain ⟨anchor, h⟩ := h
          obtain ⟨A, B, domain, rows, resultType, htype, hrow, hout, display, behavior⟩ := h
          refine ⟨anchor, A, B, domain, rows, resultType, htype, hrow, hout, display, ?_⟩
          intro Ξ γ later x y admitted
          have h := (behavior Ξ γ later x y admitted).1
          exact ⟨h, h, ih.2 _ _ _ _ _ _ h⟩

theorem TypeRelated.left_diagonal
    (H : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left left profile :=
  (left_diagonals env U registry _).1 _ _ _ _ H

theorem Related.left_diagonal
    (H : Related env U registry Γ left right type value typeProfile) :
    Related env U registry Γ left left type value typeProfile :=
  (left_diagonals env U registry _).2 _ _ _ _ _ _ H

/-- Keep the anchor-to-left evidence and its support literally; only the
argument pair's raw and semantic equalities take their left diagonal. -/
theorem Admitted.left_diagonal
    (H : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ key left left := by
  obtain ⟨hanchor, hpair, support, hinput, hsupport, htype, hfirst, hsecond⟩ := H
  exact ⟨hanchor, hpair.hasType.1, support, hinput, hsupport, htype, hfirst,
    Related.left_diagonal hsecond⟩

end Lean4Lean.AnchoredSemantics
