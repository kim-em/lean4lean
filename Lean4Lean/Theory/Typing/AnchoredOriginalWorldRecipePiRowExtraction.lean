import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePiRowExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor

/-! Resolve an actual charged Pi row without opening its children. The exact
constructed domain and body retain the same annotation worlds and head mask. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

 theorem RichCodeRecipe.requestedRowControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B)
      relevant (Profile.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sponsored : Sponsored frontier annotation.worlds)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      (.forallE C D) (Profile.pi prototypeDomain prototypeBody support rows))
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (resources : footprint.Available available) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode key result, Nonempty (row.Controlled controls frontier) := by
  obtain ⟨row, supportEq, domainFootprintEq, bodyFootprintEq, domainEq, bodyEq⟩ := recipe.requestedRowExact henv hscoped formed
    whole rfl selected admitted resources
  have domainReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := domainNode) (.domain recipe))) :=
    ⟨.recipe (.domain annotation), by
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCodeRecipe.headDepth] using within, sponsored⟩
  have bodyReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := bodyNode)
        (RichCodeRecipe.body (σ := σ.cons key.anchor) recipe selected rfl))) :=
    ⟨.recipe (WorldCodeRecipeProvenance.body (σ := σ.cons key.anchor) (parent := recipe) annotation selected rfl), by
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCodeRecipe.headDepth] using within, sponsored⟩
  refine ⟨row, ⟨?_, ?_⟩⟩
  · cases row
    simp only at supportEq domainFootprintEq domainEq ⊢
    cases supportEq
    cases domainFootprintEq
    cases eq_of_heq domainEq
    exact domainReady
  · cases row
    simp only at bodyFootprintEq bodyEq ⊢
    cases bodyFootprintEq
    cases eq_of_heq bodyEq
    exact bodyReady

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
