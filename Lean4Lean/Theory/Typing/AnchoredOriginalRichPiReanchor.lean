import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep

/-! Reanchor full rich Pi rows by the two fixed original formation children.
Both unary calls use the actual header frame's dependency environment. The
result keeps the same original body occurrence; only its realized anchor and
finite pack change. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

/-- Domain and body F are applied only at their retained original occurrences,
strictly below the Pi parent at the actual captured environment. -/
theorem RichPiRowCertificate.reanchorStep {anchor : VExpr}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (domainF : HeaderCodeInductionAt header field major env registry hf sf initial context (.ref domain) limit)
    (bodyF : HeaderCodeInductionAt header field major env registry hf sf initial (.cons context domain) body limit)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf sf initial)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (row : RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body
      (reanchorKey key anchor) result) := by
  have domainBound : (Closure.close (domain.dependencyOrigin hf)
      (frame.dependencyEnvironment hf sf initial)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_domain_cost _ [_] [] _) bound
  obtain ⟨domainAnswer⟩ := domainF target locals σ σ available frame domainBound closed formed substitutions
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
  let bodyFrame := HeaderBinderFrame.bind frame domain location lineage row.domain row.domainAvailable
    row.inputTyped arguments needs bounded covered
  have bodyBound : (Closure.close (body.dependencyOrigin hf)
      (bodyFrame.dependencyEnvironment hf sf initial)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) bound
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: headerSource) :=
    .cons substitutions (domain.sound.defeq.mono headerBelow) raw
  obtain ⟨answer⟩ := bodyF target (Locals.push locals) (σ.cons key.anchor) (σ.cons anchor)
    (available.push needs) bodyFrame bodyBound (Valuation.push_atomized_closed closed _) formed paired
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

/-- Extract a requested function row through every rich certificate wrapper.
The prefix fixes the actual exposed Pi children before any child F call. -/
theorem RichCert.piRowStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v)) (hu : u.WF U) (hv : v.WF U)
    (domainF : HeaderCodeInductionAt header field major env registry hf sf initial context (.ref domain) limit)
    (bodyF : HeaderCodeInductionAt header field major env registry hf sf initial (.cons context domain) body limit)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf sf initial)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    {node : EndpointState headerEnv U headerSource (.forallE A B) assigned}
    (route : PrefixRoute headerEnv U headerSource (.forallE A B) node (.pi hu hv (.ref domain) body))
    {profile : Profile (n + 1)}
    (certificate : RichCert headerEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile)
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) profile)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    ∃ result, Nonempty (RichPiRowCertificate env U registry target locals σ available relevant (.ref domain) body key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domainSupport, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := certificate.piOriginsWith henv hscoped formed closed
    (fun row admitted => row.reanchorStep henv headerBelow hf sf initial domain location lineage body
      domainF bodyF frame bound closed formed substitutions admitted) hu hv route resources
  exact ⟨result, certificate.piRowOfDeferredOrigins henv hscoped formed closed
    (fun row admitted => row.reanchorStep henv headerBelow hf sf initial domain location lineage body
      domainF bodyF frame bound closed formed substitutions admitted) origins member row whole admitted, resultTyped⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
