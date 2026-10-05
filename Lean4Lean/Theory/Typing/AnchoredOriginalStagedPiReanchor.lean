import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedInductionAt

/-! Reanchor full rich Pi rows using ambient-qualified induction at the two
fixed original formation children.
Both unary calls use the actual header frame's dependency environment. The
result keeps the same original body occurrence; only its realized anchor and
finite pack change. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

/-- Domain and body F are applied only at their retained original occurrences,
strictly below the Pi parent at the actual captured environment. -/
theorem RichPiRowCertificate.reanchorStaged {anchor : VExpr}
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation headerEnv U rootSource)
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initialContext =
      .cons (location.contextDerivation initialContext) domain)
    (domainF : OriginalStagedCodeInductionAt env registry stage hf initialContext location limit)
    (bodyF : OriginalStagedCodeInductionAt env registry stage hf initialContext bodyLocation limit)
    (frame : OriginalRichFrame headerEnv env U registry target (location.contextDerivation initialContext) locals σ σ available)
    (ambient : frame.Ambient)
    (sources : frame.AllSources (SourceAtStage stage))
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      (reanchorKey key anchor) result) := by
  have domainBound : (Closure.close (domain.dependencyOrigin hf)
      (frame.dependencyEnvironment hf)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_domain_cost _ [_] [] _) bound
  obtain ⟨domainAnswer⟩ := domainF target locals σ σ available frame ambient sources domainBound closed formed substitutions
    row.domain row.domainAvailable
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, pair, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainAnswer.related pair
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  let bodyFrame := OriginalRichFrame.bind frame domain row.domain row.domainAvailable
    row.inputTyped arguments needs bounded covered
  have bodyAmbient : bodyFrame.Ambient := by
    change (RawOriginalRichFrame.bind frame.raw domain row.domain row.domainAvailable
      row.inputTyped arguments needs bounded covered).Ambient
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.below, ambient⟩
  have bodySources : bodyFrame.AllSources (SourceAtStage stage) := by
    change (RawOriginalRichFrame.bind frame.raw domain row.domain row.domainAvailable
      row.inputTyped arguments needs bounded covered).AllSources _
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.source, sources⟩
  have bodyBound : (Closure.close (body.dependencyOrigin hf)
      (bodyFrame.dependencyEnvironment hf)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) bound
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: headerSource) :=
    .cons substitutions (domain.sound.defeq.mono headerBelow) raw
  have bodyF' := bodyF
  unfold OriginalStagedCodeInductionAt at bodyF'
  rw [bodyContext] at bodyF'
  obtain ⟨answer⟩ := bodyF' target (Locals.push locals) (σ.cons key.anchor) (σ.cons anchor)
    (available.push needs) bodyFrame bodyAmbient bodySources bodyBound (Valuation.push_atomized_closed closed _) formed paired
    row.body (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, coverage, resources⟩ := Footprint.pack_available answer.resources bounded covered
  exact ⟨{ row with
    anchor := admitted.reset_anchor
    bodyFootprint := answer.footprint
    body := answer.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
