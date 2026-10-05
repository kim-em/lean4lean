import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPi
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy
import Lean4Lean.Theory.Typing.AnchoredSortableCodeIntroduction
import Lean4Lean.Theory.Typing.AnchoredSortableLive

/-! Paired native Pi F retains actual assigned-sort evidence. The original
body's computational answer establishes relevance for every requested row;
code interpretation alone cannot discharge that obligation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {root : EndpointRef headerEnv U rootSource rootExpression rootType}

theorem OriginalRichFrame.piBodyComputationalStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (bodyF : OriginalComputationalInductionAt env registry hf initialContext bodyLocation limit)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    (certificate : RichCert headerEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) relevant output footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key key.anchor z) :
    Nonempty (RichComputationalValue headerEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (τ.cons z)
      (available.push (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons)) output) := by
  unfold OriginalComputationalInductionAt at bodyF
  rw [bodyLineage] at bodyF
  let needs := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  obtain ⟨_, raw, _, _, _, _, _, pair⟩ := admitted
  let localFrame := OriginalRichFrame.bind frame domain domainCode domainAvailable
    guard.inputTyped (Related.convert henv guard.inputTyped guard.domains pair) needs
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
  have localBound : (Closure.close (body.dependencyOrigin hf)
      (localFrame.dependencyEnvironment hf)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) bound
  exact bodyF target (Locals.push locals) (σ.cons key.anchor) (τ.cons z) (available.push needs)
    localFrame localBound (Valuation.push_atomized_closed closed _) formed
    (.cons substitutions (domain.sound.defeq.mono headerBelow) (guard.path.cast raw))
    (.code certificate) (pack.available_atomized_localNeeds resources)

theorem RichRows.originalPiBodySort
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (bodyF : OriginalComputationalInductionAt env registry hf initialContext bodyLocation limit)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (rows : RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient values footprint)
    (resources : footprint.Available available) :
    ∀ key output, (key, output) ∈ values →
      ∀ flag, Relevant v flag → output.HasType (.sort flag) := by
  intro key output member flag relevance
  match rows with
  | .nil => cases member
  | .cons guard certificate pack covered rest =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have headResources := fun i need present => resources i need (List.mem_append_left _ present)
      obtain ⟨answer⟩ := frame.piBodyComputationalStep henv headerBelow hf initialContext
        domain location lineage body bodyLocation bodyLineage bodyF bound closed formed substitutions
        domainCode domainAvailable guard certificate pack covered headResources guard.anchor
      exact TypeRelated.sort_typed formed relevance answer.typeCode answer.typed
    · exact rest.originalPiBodySort henv headerBelow hf initialContext domain location lineage
        body bodyLocation bodyLineage bodyF frame bound closed formed substitutions domainCode domainAvailable
        (fun i need present => resources i need (List.mem_append_right _ present)) key output member flag relevance
termination_by sizeOf rows

theorem OriginalRichFrame.nativePiComputationalStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (domainF : OriginalComputationalInductionAt env registry hf initialContext location
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalComputationalInductionAt env registry hf initialContext bodyLocation
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient values footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue headerEnv env U registry target (.pi hu hv (.ref domain) body)
      locals σ τ available (Profile.pi prototypeDomain prototypeBody ambient values)) := by
  obtain ⟨answer⟩ := frame.nativePiStep henv hscoped headerBelow hf initialContext
    domain location lineage body bodyLocation bodyLineage hu hv
    (domainF.code henv hscoped) (bodyF.code henv hscoped) closed formed substitutions
    domainCode domainAvailable guard rows resources
  obtain ⟨flag, relevance⟩ : ∃ flag, Relevant v flag := by
    by_cases zero : v ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  have typed : (Profile.pi prototypeDomain prototypeBody ambient values).HasType (.sort flag) :=
    Profile.HasType.pi_iff.mpr ⟨answer.certificate.formed.wf_value,
      fun key output member => rows.originalPiBodySort henv headerBelow hf initialContext
        domain location lineage body bodyLocation bodyLineage bodyF frame (Nat.le_refl _)
        closed formed substitutions domainCode domainAvailable resources key output member flag relevance⟩
  have imaxFlag : Relevant (.imax u v) flag := by
    cases flag <;> simpa only [Relevant, Bool.false_eq_true, if_false, if_true,
      VLevel.imax_eq_zero] using relevance
  have typeCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n + 1)
    henv (show (VLevel.imax u v).WF U from ⟨hu, hv⟩)
    (show (VLevel.imax u v).WF U from ⟨hu, hv⟩) rfl imaxFlag
  have related := Related.of_sortable_code henv answer.certificate.formed typed answer.related typeCode
  exact ⟨{
    support := .sort flag
    footprint := []
    certificate := .legacy (.seed (.sort imaxFlag) (Profile.HasType.sort flag))
    resources := fun _ _ member => nomatch member
    typed := typed
    related := related
    typeCode := typeCode
    rightQuery := {
      rank := n + 1
      bound := Nat.le_refl _
      raw := Profile.pi prototypeDomain prototypeBody ambient values
      footprint := answer.footprint
      observation := .code answer.certificate
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := answer.resources
      live := AnchoredSemantics.Profile.HasType.sortable_live answer.certificate.formed } }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
