import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiRowCertificate
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePiAlignment

/-! An interpreted, requested row of a charged recipe. Both certificates
retain the same recipe; the body explicitly demands the selected binder input.
Admission comes from the actual application request, not from Pi syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem externalPack (footprint : Footprint) :
    BinderPack n .empty (footprint.sourceLift (.skip .refl)) footprint := by
  induction footprint with
  | nil => exact .nil
  | cons head tail ih =>
    rcases head with ⟨index, need⟩
    exact .external index need ih

/-- This is an actual constructed row, including its exact finite footprint.
The interpreted Pi supplies the raw domain chain even at empty support. -/
theorem RichCodeRecipe.requestedRowExact
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B)
      relevant (Profile.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) right
      (Profile.pi prototypeDomain prototypeBody support rows))
    (rightEq : right = .forallE C D)
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (resources : footprint.Available available) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode key result,
      row.domainSupport = support ∧
      row.domainFootprint = footprint ∧
      row.bodyFootprint = ((0, ⟨n, key.input⟩) :: footprint.sourceLift (.skip .refl)) ∧
      HEq row.domain (RichCert.recipe (node := domainNode) (.domain recipe)) ∧
      HEq row.body (RichCert.recipe (node := bodyNode)
        (RichCodeRecipe.body (σ := σ.cons key.anchor) recipe selected rfl)) := by
  subst right
  obtain ⟨alignment⟩ := TypeRelated.literalPiRowAlignment henv hscoped formed
    (by simpa only [subst] using whole) selected
  have typed := (Profile.HasType.pi_iff.mp recipe.formed).1
  have inputTyped := (Profile.WF.pi_iff.mp typed).2 key result selected
  let bodyRecipe : RichCodeRecipe env U registry target (A :: source) (Locals.push locals)
      (σ.cons key.anchor) B relevant result
      ((0, ⟨n, key.input⟩) :: footprint.sourceLift (.skip .refl)) :=
    .body recipe selected rfl
  refine ⟨{ domainSupport := support
            domainFootprint := footprint
            domain := .recipe (.domain recipe)
            domainAvailable := resources
            inputTyped := inputTyped.1
            alignment := alignment
            anchor := admitted
            bodyFootprint := _
            body := .recipe bodyRecipe
            packed := (Need.atGrade n ⟨n, key.input⟩).union .empty
            outside := footprint
            pack := .local ⟨n, key.input⟩ (Nat.le_refl n) (externalPack footprint)
            covered := ?_
            outsideAvailable := resources }, rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
  intro atom member
  have grade : Need.atGrade n ⟨n, key.input⟩ = key.input := by
    simp [Need.atGrade]
  rw [grade] at member
  change atom ∈ key.input.atoms ++ [] at member
  simpa only [List.append_nil] using member

theorem RichCodeRecipe.requestedRow
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B)
      relevant (Profile.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) right
      (Profile.pi prototypeDomain prototypeBody support rows))
    (rightEq : right = .forallE C D)
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (resources : footprint.Available available) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode key result,
      HEq row.domain (RichCert.recipe (node := domainNode) (.domain recipe)) ∧
      HEq row.body (RichCert.recipe (node := bodyNode)
        (RichCodeRecipe.body (σ := σ.cons key.anchor) recipe selected rfl)) := by
  obtain ⟨row, _, _, _, domainEq, bodyEq⟩ := recipe.requestedRowExact
    henv hscoped formed whole rightEq selected admitted resources
  exact ⟨row, domainEq, bodyEq⟩

/-- Profile selection is kept inside the charged recipe. No inverse of a
lossy profile action or interpretation of its pre-action profile is used. -/
theorem RichCodeRecipe.requestedRowOfMember
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B)
      relevant (profile : Profile (n + 1)) footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      (.forallE C D) profile)
    (atomMember : (.pi prototypeDomain prototypeBody support rows) ∈ profile.atoms)
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (resources : footprint.Available available) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode key result,
      HEq row.domain (RichCert.recipe (node := domainNode)
        (.domain (.action (.select atomMember) recipe))) ∧
      HEq row.body (RichCert.recipe (node := bodyNode)
        (RichCodeRecipe.body (σ := σ.cons key.anchor)
          (.action (.select atomMember) recipe) selected rfl)) := by
  exact (RichCodeRecipe.action (.select atomMember) recipe).requestedRow
    henv hscoped formed
    ((SortableCodeAction.select (relevant := relevant) atomMember).codeMap henv hscoped whole)
    rfl selected admitted resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
