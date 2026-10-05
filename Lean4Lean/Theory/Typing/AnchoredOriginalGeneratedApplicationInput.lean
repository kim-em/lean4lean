import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationArguments
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHead
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplication

/-! The selected captured body frame already types every used local request at
its exact original domain. Its external resources are bounded by the original
base, so these domain certificates can be recovered without replaying graded
argument observations as exact observations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem typedBinderPack
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (henv : env.Ordered) (required : Footprint) (minimum : Nat)
    (head : ∀ need, (0, need) ∈ required →
      ∃ support footprint,
        Nonempty (RichCert sourceEnv env U registry target (.ref domain) locals σ true
          (support : Profile need.rank) footprint) ∧ footprint.Available available ∧
        need.profile.HasType support ∧
        TypeRelated env U registry target (A.subst σ) (A.subst σ) support ∧
        Related env U registry target left right (A.subst σ) need.profile support)
    (external : ∀ i need, (i+1, need) ∈ required → need ∈ available i) :
    Nonempty (RichTypedBinderPack domain env registry target locals σ available left right required minimum) := by
  induction required with
  | nil =>
    exact ⟨⟨minimum, Nat.le_refl _, .empty, .empty, [],
      .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))),
      (fun _ _ h => nomatch h), Profile.HasType.empty Profile.WF.empty,
      TypeRelated.of_singletons (fun _ h => nomatch h), Related.of_singletons (fun _ h => nomatch h),
      [], .nil, (fun _ _ h => nomatch h)⟩⟩
  | cons entry rest ih =>
    obtain ⟨tail⟩ := ih (fun need h => head need (List.mem_cons_of_mem _ h))
      (fun i need h => external i need (List.mem_cons_of_mem _ h))
    rcases entry with ⟨i, need⟩
    cases i with
    | succ i =>
      exact ⟨⟨tail.rank, tail.bound, tail.input, tail.support, tail.footprint,
        tail.certificate, tail.resources, tail.typed, tail.code, tail.related,
        (i, need) :: tail.outside, .external i need tail.pack,
        fun index wanted h => (List.mem_cons.mp h).elim
          (fun equal => by cases equal; exact external i need List.mem_cons_self)
          (tail.external index wanted)⟩⟩
    | zero =>
      obtain ⟨support, footprint, ⟨certificate⟩, resources, typed, code, related⟩ := head need List.mem_cons_self
      let N := max need.rank tail.rank
      have hn : need.rank ≤ N := Nat.le_max_left _ _
      have ht : tail.rank ≤ N := Nat.le_max_right _ _
      let combined := (raiseProfile N hn support).union (raiseProfile N ht tail.support)
      have firstTyped := Profile.HasType.raise hn typed
      have tailTyped := Profile.HasType.raise ht tail.typed
      have wf := firstTyped.wf_type.union tailTyped.wf_type
      have firstTyped' := firstTyped.enlarge (Profile.le_union_left _ _) wf
      have tailTyped' := tailTyped.enlarge (Profile.le_union_right _ _) wf
      have combinedCode : TypeRelated env U registry target (A.subst σ) (A.subst σ) combined := by
        apply TypeRelated.of_singletons
        intro atom member
        exact (List.mem_append.mp member).elim
          (fun h => (code.raise henv hn).singleton h)
          (fun h => (tail.code.raise henv ht).singleton h)
      refine ⟨⟨N, Nat.le_trans tail.bound ht,
        (raiseProfile N hn need.profile).union (raiseProfile N ht tail.input), combined,
        footprint ++ tail.footprint, .union (certificate.raise hn) (tail.certificate.raise ht),
        (fun i need h => (List.mem_append.mp h).elim (resources i need) (tail.resources i need)),
        firstTyped'.union tailTyped', combinedCode,
        (Related.retag henv firstTyped' combinedCode (related.raise henv hn)).union
          (Related.retag henv tailTyped' combinedCode (tail.related.raise henv ht)),
        tail.outside, ?_, tail.external⟩⟩
      simpa only [Need.atGrade, dif_pos hn] using BinderPack.local need hn (tail.pack.raise ht)


section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

/-- A demanded input has an exact certificate at the retained original
application domain, using only the original external resources. -/
theorem ApplicationBackwardQueries.headCode
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (member : need ∈ packet.footprint.localNeeds) :
    ∃ support footprint,
      Nonempty (RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile need.rank) footprint) ∧ footprint.Available available ∧
      need.profile.HasType support ∧
      Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) need.profile support := by
  let selected := packet.reply.answer.reply.realization.frame
  have found := packet.resources 0 need (Footprint.mem_localNeeds.mp member)
  obtain ⟨answer⟩ := selected.headCode henv formed found
  have positions : selected.peel.tailLocals = locals := by
    have first := selected.peel.positions
    have second := packet.reply.answer.reply.locals_eq
    change packet.reply.answer.reply.locals = Locals.push locals at second
    exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
      (List.cons.inj (first.trans second)).2
  have external : ∀ i need, need ∈ packet.reply.answer.reply.available (i + 1) → need ∈ available i := by
    intro i wanted present
    exact packet.reply.answer.capped.availableBound (i + 1) wanted present
  have identityTail : ((Subst.id.cons a).comp σ).tail = σ := by funext i; rfl
  refine ⟨answer.support, answer.footprint, ⟨?_⟩,
    (fun i wanted present => external i wanted (answer.resources i wanted present)), answer.typed, ?_⟩
  · simpa only [positions, applicationBodyDisplay, Subst.comp, Subst.cons, subst_id, identityTail] using answer.certificate
  · simpa only [applicationBodyDisplay, Subst.comp, Subst.cons, Subst.head, Subst.tail, subst_id, identityTail] using answer.related

/-- Every semantic code call is the same strictly smaller original domain
child. The selected body frame supplies the typing of the exact requests. -/
theorem ApplicationBackwardQueries.typedPack
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost) :
    Nonempty (RichTypedBinderPack domain env registry target locals σ available
      (a.subst σ) (a.subst τ) packet.footprint n) := by
  apply typedBinderPack domain henv packet.footprint n
  · intro need member
    obtain ⟨support, footprint, ⟨certificate⟩, resources, typed, related⟩ :=
      packet.headCode henv formed (Footprint.mem_localNeeds.mpr member)
    have reserve := application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
      (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)
    have smaller : (Closure.close (domain.dependencyOrigin ordered)
        (frame.leftDiagonal.dependencyEnvironment ordered)).cost <
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost := by
      rw [frame.dependencyEnvironment_leftDiagonal]
      exact Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _) reserve
    obtain ⟨answer⟩ := domainF target locals σ σ available frame.leftDiagonal smaller
      closed formed substitutions.left certificate resources
    exact ⟨support, footprint, ⟨certificate⟩, resources, typed, answer.related, related⟩
  · intro i need member
    exact packet.reply.answer.capped.availableBound (i + 1) need (packet.resources (i + 1) need member)


/-- Full nonempty and empty result profiles use the same exact original
codomain certificate. All required key requests and their original-domain
support are computed from the selected captured frame. -/
theorem ApplicationBackwardQueries.piRequest
    {n : Nat} {profile : Profile n}
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost) :
    Nonempty (GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile) := by
  obtain ⟨packed⟩ := packet.typedPack (n := n) henv hscoped formed closed domainF
  let key : Key packed.rank := ⟨A.subst σ, a.subst σ, packed.input⟩
  have raw := (argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions.left
  have related := packed.related.left_diagonal
  have guard : LambdaGuard env U registry target σ A key packed.support :=
    ⟨packed.typed, packed.certificate.formed, .refl, packed.code,
      ⟨raw, raw, packed.support, packed.typed, packed.certificate.formed, packed.code, related, related⟩⟩
  have bodyCode : RichCert sourceEnv env U registry target body (Locals.push locals)
      (σ.cons (a.subst σ)) relevant (raiseProfile packed.rank packed.bound profile) packet.footprint := by
    have positions := packet.reply.answer.reply.locals_eq
    change packet.reply.answer.reply.locals = Locals.push locals at positions
    have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
      funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
    simpa only [positions, realization] using packet.certificate.raise packed.bound
  let rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant
      packed.support [(key, raiseProfile packed.rank packed.bound profile)] (packed.outside ++ []) :=
    .cons guard bodyCode packed.pack (fun _ member => member) .nil
  exact ⟨⟨packed.rank, packed.bound, key, packed.support,
    packed.footprint ++ (packed.outside ++ []),
    .pi hu hv packed.certificate PiGuard.literal rows,
    (fun i need member => (List.mem_append.mp member).elim
      (packed.resources i need)
      (fun member => packed.external i need (by simpa only [List.append_nil] using member))),
    guard.anchor, rfl⟩⟩


noncomputable def applicationPiFormationDisplay :
    OriginalNestedDisplay U source (.forallE A B) (.sort (.imax u v)) :=
  OriginalNestedDisplay.identity (frame.captureBase substitutions) (.pi hu hv (.ref domain) body)
    (.ofLocation (.appPiFormation location) initial)

noncomputable def applicationFunctionFormationDisplay :
    OriginalNestedDisplay U source (.forallE A B) (.sort function.typeFormation.level) :=
  OriginalNestedDisplay.identity (frame.captureBase substitutions) function.typeFormation.node
    (.ofLocation (.assignedFormation (.appFunction location)) initial)

/-- The assembled Pi request is replayed to the actual function's assigned
formation using two retained original displays. At the identity base, the
query-selected result freezes back to the original resources. -/
theorem GeneratedApplicationPiRequest.atFunctionFormation
    (request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile)
    (henv : env.Ordered) (closed : available.AtomClosed)
    (formationR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationPiFormationDisplay (frame := frame) (substitutions := substitutions))
      (applicationFunctionFormationDisplay (frame := frame) (substitutions := substitutions))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument result hu hv location frame ordered)) :
    ∃ footprint,
      Nonempty (RichCert sourceEnv env U registry target function.typeFormation.node locals σ relevant
        (Profile.pi (A.subst σ) (B.subst σ.lift) request.support
          [(request.key, raiseProfile request.rank request.bound profile)]) footprint) ∧
      footprint.Available available := by
  let base := frame.captureBase substitutions
  have smaller := EndpointState.application_function_type_reindex_schedule ordered hu hv (.ref domain) body
    function argument result (frame.dependencyEnvironment ordered)
  rw [Nat.add_comm] at smaller
  obtain ⟨reply⟩ := formationR base.identityRealization base.identityCapped closed
    base.identityRealization base.identityCapped closed smaller (.code request.certificate) request.resources
  exact reply.answer.freezeBase.code henv request.certificate.formed


/-- Backwards application-prefix construction starts from the actual original
result certificate and returns the actual original function-type query.
All resource discovery, exact input typing and Pi formation are internal. -/
theorem generatedApplicationFunctionRequest
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (ordered : sourceEnv.Ordered)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
      (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument result hu hv location frame ordered))
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (formationR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationPiFormationDisplay (frame := frame) (substitutions := substitutions))
      (applicationFunctionFormationDisplay (frame := frame) (substitutions := substitutions))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument result hu hv location frame ordered))
    (certificate : RichCert sourceEnv env U registry target result locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile,
      ∃ functionFootprint,
        Nonempty (RichCert sourceEnv env U registry target function.typeFormation.node locals σ relevant
          (Profile.pi (A.subst σ) (B.subst σ.lift) request.support
            [(request.key, raiseProfile request.rank request.bound profile)]) functionFootprint) ∧
        functionFootprint.Available available := by
  obtain ⟨packet, _⟩ := generatedApplicationArguments initial domain body function argument result hu hv location frame substitutions ordered
    henv hscoped below formed closed bodyR certificate resources
  obtain ⟨request⟩ := packet.piRequest henv hscoped below formed closed domainF
  obtain ⟨functionFootprint, functionCertificate, functionResources⟩ :=
    request.atFunctionFormation (frame := frame) (substitutions := substitutions) henv closed formationR
  exact ⟨request, functionFootprint, functionCertificate, functionResources⟩


end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
