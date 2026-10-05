import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedPi
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

/-! The native dependent Pi case of the rich original fundamental induction.
Its recursive inputs are code interpretation at fixed original domain and
body locations. Every call uses the actual generic source frame, including
all retained captured owners; future worlds preserve its computed closure. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false

variable {root : EndpointRef headerEnv U rootSource rootExpression rootType}

private theorem renameCoverage {p q : Profile n}
    (covered : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (ρ : Lift) :
    ∀ atom ∈ (p.rename ρ).atoms, atom ∈ (q.rename ρ).atoms := by
  intro atom member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  exact List.mem_map_of_mem (covered old present)

private theorem admitted_from_anchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target key key.anchor x ∧
      Admitted env U registry target key key.anchor y := by
  obtain ⟨anchorRaw, pairRaw, support, typed, formed, code, anchor, pair⟩ := admitted
  have anchorSelf := Related.left_diagonal anchor
  exact ⟨⟨anchorRaw.hasType.1, anchorRaw, support, typed, formed, code, anchorSelf, anchor⟩,
    ⟨anchorRaw.hasType.1, anchorRaw.trans pairRaw, support, typed, formed, code,
      anchorSelf, Related.trans henv hscoped anchor pair⟩⟩

/-- Interpret the retained body query at an actual admitted argument. The
returned source certificate is at the very same original body occurrence. -/
theorem OriginalRichFrame.piBodyStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext bodyLocation limit)
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
    Nonempty (RichCodeTransferResult env U registry target body body (Locals.push locals)
      (σ.cons key.anchor) (τ.cons z)
      (available.push (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons)) relevant output) := by
  unfold OriginalCodeInductionAt at bodyF
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
    certificate (pack.available_atomized_localNeeds resources)

/-- Reconstruct every finite right-hand row from the body child's actual
returned queries. Packs and external footprints are computed after each call. -/
theorem RichRows.originalPiTransferStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext bodyLocation limit)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (bound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
      (frame.dependencyEnvironment hf)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (domainAnswer : RichCodeTransferResult env U registry target (.ref domain) (.ref domain)
      locals σ τ available true ambient)
    (rows : RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient values footprint)
    (resources : footprint.Available available) :
    ∃ outputFootprint,
      Nonempty (RichRows headerEnv env U registry target (.ref domain) body locals τ relevant ambient values outputFootprint) ∧
      outputFootprint.Available available := by
  match rows with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | .cons guard certificate pack covered rest =>
    have headResources := fun i need member => resources i need (List.mem_append_left _ member)
    obtain ⟨answer⟩ := frame.piBodyStep henv headerBelow hf initialContext domain location lineage body bodyLocation bodyLineage bodyF
      bound closed formed substitutions domainCode domainAvailable guard certificate pack covered headResources guard.anchor
    obtain ⟨newPacked, newOutside, newPack, newCovered, newResources⟩ := Footprint.pack_available answer.resources
      (fun need member => (pack.atomized_localNeeds need member).1)
      (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
    have raw := (domain.sound.defeq.mono headerBelow).substDF henv substitutions.wf formed substitutions
    have newGuard : LambdaGuard env U registry target τ A _ ambient :=
      ⟨guard.inputTyped, guard.formed, guard.path.trans (.single raw),
        guard.domains.trans henv domainAnswer.related, guard.anchor⟩
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailResources⟩ :=
      rest.originalPiTransferStep henv headerBelow hf initialContext domain location lineage body bodyLocation bodyLineage bodyF frame bound
        closed formed substitutions domainCode domainAvailable domainAnswer
        (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨newOutside ++ tailFootprint, ⟨.cons newGuard answer.certificate newPack newCovered tailCode⟩,
      fun i need member => (List.mem_append.mp member).elim (newResources i need) (tailResources i need)⟩

termination_by sizeOf rows

/-- The original anchor query supplies both sides' arbitrary-argument
capabilities in every future context. All three comparisons are composed
from unary body F answers under actual rich frames. -/
theorem RichRows.originalPiCapabilitiesStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext bodyLocation limit)
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
      key.input.HasType ambient ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient ∧
      ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
        Admitted env U registry Δ (key.rename ρ) x y →
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B.subst σ.lift).lift' ρ.cons).inst y) (output.rename ρ) ∧
        TypeRelated env U registry Δ (((B.subst τ.lift).lift' ρ.cons).inst x)
          (((B.subst τ.lift).lift' ρ.cons).inst y) (output.rename ρ) ∧
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B.subst τ.lift).lift' ρ.cons).inst x) (output.rename ρ) := by
  intro key output member
  match rows with
  | .nil => cases member
  | .cons guard certificate pack covered rest =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      refine ⟨guard.inputTyped, guard.path, guard.domains, ?_⟩
      intro Δ ρ future x y admitted
      have domain' := domainCode.future henv future
      have guard' := guard.future henv future
      have certificate' := certificate.future henv future
      simp only [subst_cons_future] at certificate'
      have covered' := renameCoverage covered ρ
      have headResources := fun i need present => resources i need (List.mem_append_left _ present)
      have shiftedResources := Footprint.Available.rename headResources ρ
      have leftBound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
          ((frame.leftDiagonal.future henv future).dependencyEnvironment hf)).cost ≤ limit := by
        simpa only [OriginalRichFrame.dependencyEnvironment_future,
          OriginalRichFrame.dependencyEnvironment_leftDiagonal] using bound
      have rightBound : (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
          ((frame.future henv future).dependencyEnvironment hf)).cost ≤ limit := by
        simpa only [OriginalRichFrame.dependencyEnvironment_future] using bound
      have atLeft : ∀ z, Admitted env U registry Δ (key.rename ρ) (key.rename ρ).anchor z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B.subst ((σ.lift_r ρ).cons z)) (output.rename ρ) := by
        intro z admitted
        obtain ⟨answer⟩ := (frame.leftDiagonal.future henv future).piBodyStep henv headerBelow hf initialContext
          domain location lineage body bodyLocation bodyLineage bodyF leftBound (closed.rename ρ) (future.targetWF henv)
          (substitutions.left.future henv future) domain' (domainAvailable.rename ρ) guard' certificate'
          (pack.rename ρ) covered' shiftedResources admitted
        exact answer.related
      have atRight : ∀ z, Admitted env U registry Δ (key.rename ρ) (key.rename ρ).anchor z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B.subst ((τ.lift_r ρ).cons z)) (output.rename ρ) := by
        intro z admitted
        obtain ⟨answer⟩ := (frame.future henv future).piBodyStep henv headerBelow hf initialContext
          domain location lineage body bodyLocation bodyLineage bodyF rightBound (closed.rename ρ) (future.targetWF henv)
          (substitutions.future henv future) domain' (domainAvailable.rename ρ) guard' certificate'
          (pack.rename ρ) covered' shiftedResources admitted
        exact answer.related
      obtain ⟨toLeft, toRight⟩ := admitted_from_anchor henv hscoped admitted
      have leftAtX := atLeft x toLeft
      have rightAtX := atRight x toLeft
      have pairs := And.intro
        ((leftAtX.symm henv certificate'.formed.wf_value).trans henv (atLeft y toRight))
        (And.intro ((rightAtX.symm henv certificate'.formed.wf_value).trans henv (atRight y toRight))
          ((leftAtX.symm henv certificate'.formed.wf_value).trans henv rightAtX))
      simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using pairs
    · exact rest.originalPiCapabilitiesStep henv hscoped headerBelow hf initialContext domain location lineage body bodyLocation bodyLineage bodyF
        frame bound closed formed substitutions domainCode domainAvailable
        (fun i need present => resources i need (List.mem_append_right _ present)) key output member
termination_by sizeOf rows

/-- Native Pi F at arbitrary paired substitutions and arbitrary original
dependent bodies, including empty finite row tables. No outgoing row or
future semantic result is an input: both are obtained from smaller children. -/
theorem OriginalRichFrame.nativePiStep
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
    (domainF : OriginalCodeInductionAt env registry hf initialContext location
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext bodyLocation
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient values footprint)
    (resources : footprint.Available available) :
    Nonempty (RichCodeTransferResult env U registry target (.pi hu hv (.ref domain) body) (.pi hu hv (.ref domain) body)
      locals σ τ available relevant (Profile.pi prototypeDomain prototypeBody ambient values)) := by
  unfold OriginalCodeInductionAt at domainF
  rw [lineage] at domainF
  obtain ⟨domainAnswer⟩ := domainF target locals σ τ available frame (binder_domain_cost _ _ _ _)
    closed formed substitutions domainCode domainAvailable
  obtain ⟨rowFootprint, ⟨rowCode⟩, rowResources⟩ := rows.originalPiTransferStep henv headerBelow hf initialContext
    domain location lineage body bodyLocation bodyLineage bodyF frame (Nat.le_refl _) closed formed substitutions
    domainCode domainAvailable domainAnswer resources
  have caps := rows.originalPiCapabilitiesStep henv hscoped headerBelow hf initialContext domain location lineage
    body bodyLocation bodyLineage bodyF frame (Nat.le_refl _) closed formed substitutions domainCode domainAvailable resources
  have originalDomain := domain.sound.defeq.mono headerBelow
  have originalBody := body.sound.defeq.mono headerBelow
  have hA := originalDomain.subst henv substitutions.left formed
  have hA' := originalDomain.subst henv (substitutions.right henv formed) formed
  have rawDomains := originalDomain.substDF henv substitutions.wf formed substitutions
  have sourceA : OnCtx (A :: headerSource) (env.IsType U) := ⟨substitutions.wf, _, originalDomain⟩
  have targetA : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨formed, _, hA⟩
  have rawBodies := originalBody.substDF henv sourceA targetA (substitutions.lift henv originalDomain)
  have hB' := originalBody.subst henv ((substitutions.right henv formed).lift henv originalDomain)
    ⟨formed, _, hA'⟩
  have rightGuard : PiGuard env U target τ A B prototypeDomain prototypeBody := {
    domainPath := (TypeConversion.single rawDomains.symm).trans guard.domainPath
    bodyPath := TypeConversion.changeDomain henv formed hA' hA (.single rawDomains.symm)
      ((TypeConversion.single rawBodies.symm).trans guard.bodyPath) }
  refine ⟨⟨domainAnswer.footprint ++ rowFootprint,
    .pi hu hv domainAnswer.certificate rightGuard rowCode,
    fun i need member => (List.mem_append.mp member).elim (domainAnswer.resources i need) (rowResources i need), ?_⟩⟩
  apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA'⟩ ⟨_, rawBodies.hasType.1⟩ ⟨_, hB'⟩
    (.single rawDomains) (.single rawBodies) guard.domainPath guard.bodyPath domainAnswer.related
  · intro key output member
    have cap := caps key output member
    exact ⟨ambient, cap.1, domainCode.formed, Profile.le_refl _, cap.2.1, cap.2.2.1⟩
  · intro key output member
    exact (caps key output member).2.2.2

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
