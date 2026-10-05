import Lean4Lean.Theory.Typing.AnchoredOriginalCappedFirstParameterCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterCells
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureRealization

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The first-slot producer supplies an actual initial frame for a dependent
next-cell query. Its paired raw substitution is reconstructed from the
original owner typing and the computed declaration path, not an alignment
hypothesis about a newly chosen owner. -/
theorem CappedFirstParameterSlot.priorFrame
    {sourceEnv headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U [] A (.sort level)}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available}
    {nominal : EndpointState sourceEnv U source argument assigned}
    {provenance : EndpointProvenance context nominal}
    {ordered : sourceEnv.Ordered}
    (slot : CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major)
      domain graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture (input : Profile n))
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env) :
    ∃ entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
        [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ),
      (⟨entry.rank, entry.input⟩ : Need) = ⟨n, (input : Profile n)⟩ ∧
      Nonempty (OriginalFrameExtension ownerFrame.raw entry.frame.raw) ∧
      ∃ prior : ParameterReplyFrame base commonCaps
          (.capture (.empty common) domain graph nominal provenance) commonLeft commonRight,
        prior.locals = Locals.push [] ∧ prior.available = (Valuation.push (RichGroupedCapture.needs [entry]) (fun _ => [])) ∧
        ∀ hf : headerEnv.Ordered, prior.realization.frame.dependencyEnvironment hf =
          ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight)
              (locals := []) (available := fun _ => [])).group domain ordered ownerInitial [entry]).dependencyEnvironment hf := by
  obtain ⟨entry, inputEq, extension, capped⟩ := slot
  let frame := (OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight)
    (locals := []) (available := fun _ => [])).group domain ordered ownerInitial [entry]
  have rawPair := (entry.owner.node.sound.defeq.mono sourceBelow).substDF henv
    entry.substitutions.wf formed entry.substitutions
  rw [entry.left_eq, entry.right_eq] at rawPair
  have declaredPair := entry.answer.path.cast rawPair
  have substitutions : Ctx.SubstEq env U target
      (commonLeft.cons (rawCapture.subst σ)) (commonRight.cons (rawCapture.subst τ)) [A] :=
    .cons .nil (domain.sound.defeq.mono headerBelow) declaredPair
  obtain ⟨realized, realizedCapped, same⟩ := capped.realize frame substitutions
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  have nextClosed : Valuation.AtomClosed (Valuation.push (RichGroupedCapture.needs [entry]) (fun _ => [])) := by
    simpa only [RichGroupedCapture.needs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      captureNeeds] using Valuation.push_atomized_closed closed [⟨entry.rank, entry.input⟩]
  exact ⟨entry, inputEq, extension,
    ⟨Locals.push [], (Valuation.push (RichGroupedCapture.needs [entry]) (fun _ => [])), realized, realizedCapped, nextClosed⟩,
    rfl, rfl, same⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
