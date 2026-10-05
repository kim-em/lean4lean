import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientGeneratedApplicationArguments
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentPack
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPiTypeReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbientDiagonal

/-! Build the application input and whole-Pi query using only actual
ambient-qualified original calls at their strict child schedules. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typedBinderPack from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

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

theorem ApplicationBackwardQueries.typedPackAmbient
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit) :
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
    have scheduled := Nat.lt_of_lt_of_le (richSchedule_strict smaller .fundamental .fundamental) budget
    obtain ⟨value⟩ := bank.computational ordered ambient.below initial (.appDomain location)
      target locals σ σ available frame.leftDiagonal ambient.leftDiagonal scheduled
      closed formed substitutions.left (.code certificate) resources
    obtain ⟨answer⟩ := value.code henv hscoped formed certificate.formed
    exact ⟨support, footprint, ⟨certificate⟩, resources, typed, answer.related, related⟩
  · intro i need member
    exact packet.reply.answer.capped.availableBound (i + 1) need (packet.resources (i + 1) need member)


theorem ApplicationBackwardQueries.piRequestWithArgumentAmbient
    {n : Nat} {profile : Profile n}
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit)
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds) :
    Nonempty (GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile) := by
  obtain ⟨packed⟩ := packet.typedPackAmbient (n := n) henv hscoped formed closed ambient bank budget
  obtain ⟨argumentQuery⟩ := binderPackArgumentQuery henv hscoped formed packed.pack supply
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
  let request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile :=
    ⟨packed.rank, packed.bound, key, packed.support,
      packed.footprint ++ (packed.outside ++ []),
      .pi hu hv packed.certificate PiGuard.literal rows,
      (fun i need member => (List.mem_append.mp member).elim
        (packed.resources i need)
        (fun member => packed.external i need (by simpa only [List.append_nil] using member))),
      guard.anchor, rfl⟩
  exact ⟨⟨request, argumentQuery, packed.footprint, packed.certificate,
    packed.resources, packed.typed, packed.code⟩⟩

end

theorem OriginalApplicationTypeRouteSide.piRequestReplyAmbient
    (side : OriginalApplicationTypeRouteSide U common)
    {base : OriginalCaptureBase env U registry target}
    (frame : OriginalCaptureRealization side.graph env registry target locals commonLeft commonRight available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight side.graph frame.frame.raw)
    (ordered : side.sourceEnv.Ordered)
    (frameBound : environmentCost (frame.frame.dependencyEnvironment ordered) ≤ capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (request : GeneratedApplicationPiRequest side.domain side.body side.hu side.hv
      env registry target locals (side.raw.comp commonLeft) available side.a true (profile : Profile n))
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : richSchedule .fundamental ((side.node.dependencyOrigin ordered).weight * (1 + capacity)) ≤ limit) :
    Nonempty (AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft)) side.pi.display commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      capacity) := by
  have smaller : (Closure.close
      ((EndpointState.pi side.hu side.hv (.ref side.domain) side.body).dependencyOrigin ordered)
      (frame.frame.leftDiagonal.dependencyEnvironment ordered)).cost <
      (side.node.dependencyOrigin ordered).weight * (1 + capacity) := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    exact Nat.lt_of_lt_of_le
      (EndpointState.appPiFormation_dependency_cost_lt ordered side.hu side.hv (.ref side.domain)
        side.body side.function side.argument side.result _)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left frameBound 1))
  have scheduled := Nat.lt_of_lt_of_le (richSchedule_strict smaller .fundamental .fundamental) budget
  obtain ⟨value⟩ := bank.computational ordered generated.ambient.1.below side.initial (.appPiFormation side.location)
    target locals (side.raw.comp commonLeft) (side.raw.comp commonLeft) available
    frame.frame.leftDiagonal generated.ambient.2.leftDiagonal scheduled closed formed frame.substitutions.left
    (.code request.certificate) request.resources
  obtain ⟨meaning⟩ := value.code henv hscoped formed request.certificate.formed
  refine ⟨{
    reply := {
      answer := {
        reply := {
          locals := locals, available := available, realization := frame
          generated := generated.capped.generated
          query := {
            rank := request.rank + 1, bound := Nat.le_refl _, raw := _
            footprint := request.footprint, observation := .code request.certificate
            adapter := by rw [raiseProfile_self]; exact .refl _
            resources := request.resources
            live := Profile.HasType.sortable_live request.certificate.formed }
          closed := closed }
        capped := generated.capped }
      bounded := fun _ => frameBound }
    related := ?_
    path := ?_, generation := generated }⟩
  · simpa only [OriginalApplicationTypeRouteSide.pi, OriginalPiTypeRouteSide.display,
      OriginalNestedDisplay.ofOccurrence, subst_subst] using meaning.related
  · simp only [OriginalApplicationTypeRouteSide.pi, subst_subst]
    exact .refl


/-- Connected application producer: the original result certificate
computes the raw argument query and the nonempty whole-Pi request, and the
actual stored Pi-formation child supplies its initial semantic reply. -/
theorem generatedAmbientApplicationPiReply
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
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
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit)
    (certificate : RichCert sourceEnv env U registry target result locals σ true (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available true profile,
      Nonempty (AmbientBoundedParameterReply (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
        ((VExpr.forallE A B).subst σ)
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location (.identity _)).pi.display
        σ τ (Profile.pi (A.subst σ) (B.subst σ.lift) packed.request.support
          [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)])
        (environmentCost (frame.dependencyEnvironment ordered))) := by
  obtain ⟨packet, ⟨supply⟩⟩ := generatedAmbientApplicationArguments initial domain body function argument result hu hv location
    frame substitutions ordered henv hscoped formed closed ambient bank budget certificate resources
  obtain ⟨packed⟩ := packet.toApplicationBackwardQueries.piRequestWithArgumentAmbient
    henv hscoped ambient.below formed closed ambient bank budget supply
  refine ⟨packed, ?_⟩
  let base := frame.captureBase substitutions
  let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv location (.identity _)
  exact side.piRequestReplyAmbient base.identityRealization (.identity ambient) ordered (Nat.le_refl _)
    henv hscoped formed closed packed.request bank budget

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
