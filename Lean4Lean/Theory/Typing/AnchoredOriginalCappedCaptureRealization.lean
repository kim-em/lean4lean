import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! Concrete realization producers for generated common scope. They preserve
actual source frames and their computed closure environments. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Package the same constructed frame using the full substitution equations
already proved by generation. This introduces no semantic retyping. -/
theorem CappedCaptureGenerated.realize
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ result : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available,
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph result.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        result.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  obtain ⟨left, right⟩ := generated.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, fun _ => rfl⟩

/-- Enter a fresh common source binder using the actual independent original
domain and rich source frame on this side. The displayed annotation need
not have an original proof in any common source environment. -/
theorem OriginalCaptureRealization.bindCapped
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.frame.raw)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (sourceBelow : sourceEnv ≤ env)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft) true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst (raw.comp commonLeft)) input support)
    (rawArguments : env.IsDefEq U target x y (A.subst (raw.comp commonLeft)))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∃ next : OriginalCaptureRealization (.bind graph domain annotation displayed) env registry target
        (Locals.push locals) (commonLeft.cons x) (commonRight.cons y) (available.push needs),
      CappedCaptureGenerated base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed) next.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered =
          .close (domain.dependencyOrigin ordered) (tail.frame.dependencyEnvironment ordered) ::
            tail.frame.dependencyEnvironment ordered := by
  let next := tail.frame.bind domain certificate resources typed arguments needs bounded covered
  have nextGenerated : CappedCaptureGenerated base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
      (.bind graph domain annotation displayed) next.raw :=
    .bind generated domain annotation displayed certificate resources typed arguments needs bounded covered
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons x) ((raw.comp commonRight).cons y) (A :: source) :=
    .cons tail.substitutions (domain.sound.defeq.mono sourceBelow) rawArguments
  obtain ⟨result, resultGenerated, same⟩ := nextGenerated.realize next substitutions
  exact ⟨result, resultGenerated, same⟩

/-- Source weakening below a fresh common binder preserves the exact source
frame, including every original captured owner. -/
theorem OriginalCaptureRealization.weakenCapped
    {base : OriginalCaptureBase env U registry target}
    {commonCaps nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (previous : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph previous.frame.raw)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
    ∃ result : OriginalCaptureRealization (.weaken graph insertion) env registry target
        locals nextLeft nextRight available,
      CappedCaptureGenerated base nextCaps nextLeft nextRight (.weaken graph insertion) result.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        result.frame.dependencyEnvironment ordered = previous.frame.dependencyEnvironment ordered :=
  (CappedCaptureGenerated.weaken generated insertion leftTail rightTail capsTail).realize
    previous.frame previous.substitutions

theorem CappedCaptureGenerated.groupOfValues
    {base : OriginalCaptureBase env U registry target}
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
      {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
      (ownerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (seedExtension : OriginalFrameExtension ownerFrame seed.frame.raw)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw))
      (leftEq : leftValue = rawCapture.subst ownerLeft)
      (rightEq : rightValue = rawCapture.subst ownerRight) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries)) := by
  cases leftEq
  cases rightEq
  exact .group generated domain ownerGenerated nominalGraph nominal provenance displayed
    ownerOrdered ownerInitial seed seedExtension entries owners



end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
