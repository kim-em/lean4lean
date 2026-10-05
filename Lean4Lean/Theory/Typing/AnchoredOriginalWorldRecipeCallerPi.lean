import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipePiRowExtraction

/-! Execute a requested charged Pi row at the caller's actual Pi originals.
Foreign canonical roots stay charged inside the two child certificates. The
new binder frame, its ancestry and both recursive call controls are entirely
caller-side; no foreign header history is coerced to the caller prefix. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- One enclosing bank computes the parent semantics by opening its charged
root. It then enters a real caller body using a real requested anchor. No F
call at the unchanged caller Pi and no all-row admission premise is used. -/
theorem WorldCodeRecipeProvenance.enterCallerBodyFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.pi hu hv (.ref domain) body))
    (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial)
      locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (paid : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {n : Nat} {support result : Profile n} {key : Key n} {rows : List (Key n × Profile n)}
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B) relevant
      (.pi prototypeDomain prototypeBody support rows) footprint)
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sources : annotation.Sources P)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (resources : footprint.Available available)
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body key result,
    ∃ execution : RichPiRowBodyExecution (P := P)
      (context := location.contextDerivation initial) controls frontier domain body row τ key.anchor hu hv captured,
      HEq row.domain (RichCert.recipe (node := .ref domain) (.domain recipe)) ∧
      HEq row.body (RichCert.recipe (node := body)
        (RichCodeRecipe.body (σ := σ.cons key.anchor) recipe selected rfl)) ∧
      TypeRelated env U registry target (B.subst (σ.cons key.anchor))
        (B.subst (τ.cons key.anchor)) result := by
  obtain ⟨_, _, _, _, whole⟩ := annotation.rebuildFromBank henv hscoped formed
    (.pi hu hv (.ref domain) body) controls captured frontier paid sources sponsored bounded
    frame substitutions resources bank
  have wholePi : TypeRelated env U registry target
      (.forallE (A.subst σ) (B.subst σ.lift)) (.forallE (A.subst τ) (B.subst τ.lift))
      (.pi prototypeDomain prototypeBody support rows) := by
    simpa only [subst] using whole
  obtain ⟨row, supportEq, domainFootprintEq, bodyFootprintEq, domainEq, bodyEq⟩ :=
    recipe.requestedRowExact (domainNode := .ref domain) (bodyNode := body)
      henv hscoped formed wholePi rfl selected admitted resources
  have domainReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := .ref domain) (.domain recipe))) := {
    annotation := .recipe (.domain annotation)
    within := by
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCodeRecipe.headDepth,
        RichCodeRecipe.stratifiedDepth] using bounded
    sponsored := sponsored }
  have bodyReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := body)
        (RichCodeRecipe.body (σ := σ.cons key.anchor) recipe selected rfl))) := {
    annotation := .recipe (WorldCodeRecipeProvenance.body (σ := σ.cons key.anchor)
      (parent := recipe) annotation selected rfl)
    within := by
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCodeRecipe.headDepth,
        RichCodeRecipe.stratifiedDepth] using bounded
    sponsored := sponsored }
  have ready : row.Controlled controls frontier := by
    constructor
    · cases row
      dsimp only at supportEq domainFootprintEq domainEq ⊢
      cases supportEq
      cases domainFootprintEq
      cases eq_of_heq domainEq
      exact domainReady
    · cases row
      dsimp only at bodyFootprintEq bodyEq ⊢
      cases bodyFootprintEq
      cases eq_of_heq bodyEq
      exact bodyReady
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  obtain ⟨execution⟩ := row.enterBodyWorld initial henv hscoped sourceBelow controls
    domain (.piDomain location) body (.piBody location) bodyContext hu hv frame captured frontier
    data bank paid closed formed substitutions ready admitted
  have bodyRelated := (TypeRelated.literalPiBody_pair henv hscoped formed wholePi selected admitted).2
  exact ⟨row, execution, domainEq, bodyEq, by simpa only [inst_lift_cons] using bodyRelated⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
