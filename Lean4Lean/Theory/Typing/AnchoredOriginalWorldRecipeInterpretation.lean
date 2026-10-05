import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance

/-! The actual recipe reconstruction preserves the exact retained canonical
annotation and its sponsor list. Reanchoring rows changes only finite code
actions; variable resource transfers retain their own concrete observations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem WorldLegacyObsProvenance.variableRequery
    {query : Obs env U registry target locals σ (.bvar index) profile footprint}
    (annotation : WorldLegacyObsProvenance strata query) (τ : Subst) :
    ∃ next : WorldLegacyObsProvenance strata (variableRequery query τ),
      next.worlds = annotation.worlds := by
  match annotation with
  | .var locals σ index demand =>
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.var locals τ index demand, rfl⟩
  | .empty =>
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.empty, rfl⟩
  | .union left right al ar =>
    obtain ⟨bl, le⟩ := al.variableRequery τ
    obtain ⟨br, re⟩ := ar.variableRequery τ
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.union _ _ bl br, by
      change bl.worlds ++ br.worlds = al.worlds ++ ar.worlds
      rw [le, re]⟩
  | .view source change child =>
    obtain ⟨next, same⟩ := child.variableRequery τ
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.view _ change next, by
      change next.worlds = child.worlds
      exact same⟩
  | .pad source child =>
    obtain ⟨next, same⟩ := child.variableRequery τ
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.pad _ next, by
      change next.worlds = child.worlds
      exact same⟩
  | .unpad source child =>
    obtain ⟨next, same⟩ := child.variableRequery τ
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.unpad _ next, by
      change next.worlds = child.worlds
      exact same⟩
  | .rowShift source child =>
    obtain ⟨next, same⟩ := child.variableRequery τ
    rw [OriginalRecordSource.variableRequery.eq_def]
    exact ⟨.rowShift _ next, by
      change next.worlds = child.worlds
      exact same⟩
termination_by sizeOf annotation

theorem WorldRecipeResourceProvenance.requery
    {transfer : RecipeResourceTransfer env U registry target locals σ required footprint}
    (annotation : WorldRecipeResourceProvenance strata transfer) (τ : Subst) :
    ∃ next : WorldRecipeResourceProvenance strata (transfer.requery τ),
      next.worlds = annotation.worlds := by
  match transfer, annotation with
  | _, .nil => exact ⟨.nil, rfl⟩
  | _, .cons head rest =>
    obtain ⟨nextHead, headEq⟩ := head.variableRequery τ
    obtain ⟨nextRest, restEq⟩ := rest.requery τ
    exact ⟨.cons nextHead nextRest, by
      simp only [WorldRecipeResourceProvenance.worlds, headEq, restEq]⟩
termination_by sizeOf annotation

/-- The annotation determines precisely which original root can be opened. -/
def WorldCodeRecipeProvenance.Calls
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (parentKey : EquationControlMeasure.Key strata.rules.length) : Prop :=
  match annotation with
  | .root _ _ _ owner node _ _ _ certificate _ _ _ _ =>
      RecipeRootCall owner node certificate parentKey
  | .domain child | .body child _ _ | .fixedBody child _ _ |
    .resources child _ | .action _ child => child.Calls parentKey

/-- Keep the reconstructed recipe and its annotation together. The caller's
actual resources discharge every body/transfer requirement; only original F
at a computed smaller canonical root remains an induction hypothesis. -/
theorem WorldCodeRecipeProvenance.rebuildWorld
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : annotation.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint) :
    ∃ next : RichCodeRecipe env U registry target source locals τ expression relevant profile footprint,
      ∃ nextAnnotation : WorldCodeRecipeProvenance strata next,
      nextAnnotation.worlds = annotation.worlds ∧
      (∀ policy, next.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate available child controls provenance =>
    obtain ⟨_, _, related⟩ := (RichRecipeCalls.root owner node closed expressionEq
      certificate available calls).rebuild henv hscoped formed cutoff cutoffBound fuel
        constants callerSchedule bounded substitutions resources
    exact ⟨.root source locals τ owner node closed expressionEq realization certificate available,
      .root source locals τ owner node closed expressionEq realization certificate available child controls provenance,
      rfl, (fun _ => by simp only [RichCodeRecipe.headDepth]), related⟩
  | .domain child =>
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls
      (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded)
      substitutions resources
    exact ⟨.domain next, .domain nextAnnotation,
      (by change nextAnnotation.worlds = child.worlds; exact worlds),
      (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy),
      TypeRelated.literalPiDomain henv hscoped formed (by simpa only [subst] using whole)⟩
  | .fixedBody child selected admitted =>
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls
      (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded)
      substitutions resources
    have bodies := TypeRelated.literalPiBody_pair henv hscoped formed
      (by simpa only [subst] using whole) selected admitted
    exact ⟨.fixedBody next selected admitted, .fixedBody nextAnnotation selected admitted,
      (by change nextAnnotation.worlds = child.worlds; exact worlds),
      (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy),
      by simpa only [lift_subst_lift, inst_lift] using bodies.2⟩
  | .action change child =>
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls
      (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded)
      substitutions resources
    exact ⟨.action change next, .action change nextAnnotation,
      (by change nextAnnotation.worlds = child.worlds; exact worlds),
      (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy),
      change.codeMap henv hscoped whole⟩
  | .resources (transfer := transfer) child transferAnnotation =>
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls (by
      intro control active
      apply Nat.le_trans (Nat.le_max_left _ _)
      simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded control active)
      substitutions (transfer.realize henv hscoped formed resources)
    obtain ⟨nextTransfer, transferEq⟩ := transferAnnotation.requery τ
    refine ⟨.resources next (transfer.requery τ), .resources nextAnnotation nextTransfer,
      ?_, ?_, whole⟩
    · change nextAnnotation.worlds ++ nextTransfer.worlds = child.worlds ++ transferAnnotation.worlds
      rw [worlds, transferEq]
    · intro policy
      simp only [RichCodeRecipe.headDepth, transfer.requery_headDepth, depth]
  | @WorldCodeRecipeProvenance.body _ _ _ _ _ source locals A B relevant prototypeDomain prototypeBody
      n support rows footprint key result σ parent child selected anchor =>
    have previous : RecipeResourceRealization env U registry target source σ.tail τ.tail footprint := by
      intro index need member assigned lookup
      obtain ⟨value⟩ := resources (index + 1) need
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(index, need), member, rfl⟩))
        assigned.lift (.succ lookup)
      exact ⟨by simpa only [lift_subst, Subst.tail] using value⟩
    have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
      cases substitutions with
      | cons tail _ _ => exact tail
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls
      (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded)
      tailSubstitutions previous
    obtain ⟨argument⟩ := resources 0 _ List.mem_cons_self A.lift (.zero (Γ := source) (ty := A))
    have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := A))
    have paired : Related env U registry target (σ 0) (τ 0) (A.subst σ.tail)
        key.input argument.support := by simpa only [lift_subst] using argument.related
    rw [lift_subst] at raw
    have admitted := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
      (by simpa only [subst] using whole) selected anchor raw paired
    let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
    let change : AtomView env U registry target (n := n + 1)
        (.fn key unused) (.fn (reanchorKey key (τ 0)) unused) := .reanchor admitted
    let widened : RichCodeRecipe env U registry target source locals τ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support
          (reanchorRows key (reanchorKey key (τ 0)) rows)) footprint :=
      .action (.map change) next
    have result := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
      (by simpa only [subst] using whole) selected anchor raw paired
    have leftEq : σ.tail.cons (σ 0) = σ := by funext i; cases i <;> rfl
    have rightEq : τ.tail.cons (τ 0) = τ := by funext i; cases i <;> rfl
    let nextSelected := reanchorRows.changed (newKey := reanchorKey key (τ 0)) selected
    refine ⟨.body (key := reanchorKey key (τ 0)) widened nextSelected rfl,
      .body (.action (.map change) nextAnnotation) nextSelected rfl,
      ?_, (fun policy => by simpa only [RichCodeRecipe.headDepth, widened] using depth policy), ?_⟩
    · change nextAnnotation.worlds = child.worlds
      exact worlds
    · simpa only [inst_lift_cons, leftEq, rightEq] using result
termination_by sizeOf annotation

/-- Actual caller-frame entry, returning the certificate and its precise
retained annotation together. Both resource and control preservation apply to
this same output certificate. -/
theorem WorldCodeRecipeProvenance.rebuildCertificate
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : annotation.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (node : EndpointState nodeEnv U source expression assigned) :
    ∃ certificate : RichCert nodeEnv env U registry target node locals τ relevant profile footprint,
      ∃ nextAnnotation : WorldCertProvenance strata certificate,
      nextAnnotation.worlds = annotation.worlds ∧
      (∀ policy, certificate.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile ∧
      WithinAbove cutoff fuel
        (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control) := by
  obtain ⟨next, nextAnnotation, worlds, sameDepth, related⟩ := annotation.rebuildWorld henv hscoped formed
    cutoff cutoffBound fuel constants callerSchedule calls bounded substitutions
    (frame.recipeResources henv hscoped formed resources)
  refine ⟨.recipe next, .recipe nextAnnotation, ?_, ?_, related, ?_⟩
  · change nextAnnotation.worlds = annotation.worlds
    exact worlds
  · intro policy
    simpa only [RichCert.headDepth] using sameDepth policy
  · intro control active
    simpa only [RichCert.stratifiedDepth, RichCert.headDepth, sameDepth,
      RichCodeRecipe.stratifiedDepth] using bounded control active

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
