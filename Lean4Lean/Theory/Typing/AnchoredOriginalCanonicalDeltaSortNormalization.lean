import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaElimination
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank

/-! A literal-sort result of a canonical elimination does not retain its
otherwise vacuous binder demands. The actual semantic interpretation determines
each requested sort flag and reconstructs a finite ordinary source query with
empty footprint and zero depth for every computational-head policy. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem TypeRelated.literalSortObservation
    (formed : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort level) right (profile : Profile n)) :
    ∃ query : Obs env U registry target locals σ (.sort level) profile [],
      ∀ policy, query.headDepth policy = 0 := by
  induction n with
  | zero =>
    induction profile with
    | nil => exact ⟨.empty, fun _ => by simp only [Obs.headDepth]⟩
    | cons flag tail ih =>
      have flagCode := related target .refl (.refl formed) flag (by simpa only [Profile.rename_refl, Profile.atoms] using (List.mem_cons_self (a := flag) (l := tail)))
      have relevant : Relevant level flag := flagCode.literal_relevant
      have tailCode : TypeRelated env U registry target (.sort level) right tail :=
        TypeRelated.of_singletons fun atom member =>
          related.singleton (List.mem_cons_of_mem _ member)
      obtain ⟨rest, depth⟩ := ih tailCode
      refine ⟨.union (.sort relevant) rest, ?_⟩
      intro policy
      simp only [Obs.headDepth, depth, Nat.max_self]
  | succ n ih =>
    have atomic (atom : Atom (n + 1))
        (code : TypeRelated env U registry target (.sort level) right (.singleton atom)) :
        ∃ query : Obs env U registry target locals σ (.sort level) (.singleton atom) [],
          ∀ policy, query.headDepth policy = 0 := by
      have capability := code target .refl (.refl formed) atom (by simpa only [Profile.rename_refl, Profile.atoms, Profile.singleton, Profile.mk] using (List.mem_singleton_self atom))
      simp only [lift'_refl] at capability
      cases atom with
      | sort flag => exact ⟨.sort capability.literal_relevant, fun _ => by simp only [Obs.headDepth]⟩
      | fn | ctor | record => exact capability.elim
      | pi A B domain rows =>
        obtain ⟨witness⟩ := capability
        have impossible := witness.leftExposure.literalSort_head
        contradiction
      | family demand =>
        obtain ⟨witness⟩ := capability
        have impossible := congrArg (fun expression => expression.getAppFnArgs.1)
          witness.leftExposure.literalSort_head
        have head := VExpr.getAppFnArgs_mkApps_head
          (.const demand.name witness.leftLevels) witness.leftArguments
        rw [head] at impossible
        contradiction
      | pad atom =>
        obtain ⟨query, depth⟩ := ih capability
        exact ⟨.pad query, fun policy => by simpa only [Obs.headDepth] using depth policy⟩
    induction profile with
    | nil => exact ⟨.empty, fun _ => by simp only [Obs.headDepth]⟩
    | cons atom tail ihTail =>
      obtain ⟨head, headDepth⟩ := atomic atom (related.singleton List.mem_cons_self)
      have tailCode : TypeRelated env U registry target (.sort level) right tail :=
        TypeRelated.of_singletons fun atom member =>
          related.singleton (List.mem_cons_of_mem _ member)
      obtain ⟨rest, depth⟩ := ihTail tailCode
      refine ⟨.union head rest, ?_⟩
      intro policy
      simp only [Obs.headDepth, headDepth, depth, Nat.max_self]

/-- The reconstructed query belongs to the actual destination original.
No destination Pi parent, capture owner, or argument interpretation is used. -/
theorem TypeRelated.literalSortCertificate
    {node : EndpointState sourceEnv U source (.sort level) assigned}
    (formed : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort level) right (profile : Profile n))
    (sorted : profile.HasType (.sort relevant)) :
    ∃ query : RichCert sourceEnv env U registry target node locals σ relevant profile [],
      ∀ policy, query.headDepth policy = 0 := by
  obtain ⟨observation, depth⟩ := TypeRelated.literalSortObservation (locals := locals) (σ := σ) formed related
  refine ⟨.legacy (.seed observation sorted), ?_⟩
  intro policy
  simpa only [RichCert.headDepth, SortableCert.headDepth] using depth policy

theorem TypeRelated.literalSortCertificateAt
    {node : EndpointState sourceEnv U source expression assigned}
    (literal : expression = .sort level)
    (formed : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort level) right (profile : Profile n))
    (sorted : profile.HasType (.sort relevant)) :
    ∃ query : RichCert sourceEnv env U registry target node locals σ relevant profile [],
      ∀ policy, query.headDepth policy = 0 := by
  subst expression
  exact TypeRelated.literalSortCertificate formed related sorted

/-- The existing R capacity is respected exactly: the destination realization
and its positive generation witness are retained unchanged. -/
theorem TypeRelated.literalSortReply
    (display : OriginalNestedDisplay U common expression assigned)
    (literal : display.sourceExpression = .sort level)
    (formed : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort level) right (profile : Profile n))
    (sorted : profile.HasType (.sort relevant))
    (frame : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight display.graph frame.frame.raw)
    (closed : available.AtomClosed) (ordered : display.sourceEnv.Ordered) :
    ∃ reply : SourceBoundedGeneratedQueryReply P base caps display commonLeft commonRight profile
        (environmentCost (frame.frame.dependencyEnvironment ordered)),
      HEq reply.answer.reply.realization frame ∧
      ∀ policy, reply.answer.reply.query.observation.headDepth policy = 0 := by
  obtain ⟨certificate, depth⟩ := TypeRelated.literalSortCertificateAt (node := display.node)
    (locals := locals) (σ := display.raw.comp commonLeft) literal formed related sorted
  let query : RichGradedResult display.sourceEnv env U registry target display.node
      locals (display.raw.comp commonLeft) available profile := {
    rank := n
    bound := Nat.le_refl _
    raw := profile
    footprint := []
    observation := .code certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ member => nomatch member
    live := Profile.HasType.sortable_live sorted }
  refine ⟨{
    answer := {
      reply := {
        locals := locals
        available := available
        realization := frame
        generated := generated.ambientGenerated.capped.generated
        query := query
        closed := closed }
      capped := generated.ambientGenerated.capped }
    bounded := fun _ => Nat.le_refl _
    generation := generated }, HEq.rfl, ?_⟩
  intro policy
  simpa only [query, RichObs.headDepth] using depth policy

/-- Normalize the actual selected recipe by opening only its canonical root
and looking up its source-frame demands. The resulting sort certificate has
no binder demands, so captured-argument replay is unnecessary for this case. -/
theorem CanonicalDeltaElimination.normalizeSort
    (recipe : CanonicalDeltaElimination env U registry target strata source σ (.sort level)
      relevant profile footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.depth)
    (calls : recipe.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    {destination : EndpointState destinationEnv U destinationSource (.sort level) assigned}
    (destinationLocals : List Nat) (destinationSubstitution : Subst) :
    ∃ query : RichCert destinationEnv env U registry target destination destinationLocals
        destinationSubstitution relevant profile [],
      ∀ policy, query.headDepth policy = 0 := by
  have related := recipe.interpret henv hscoped formed cutoff cutoffBound fuel constants
    callerSchedule bounded calls frame substitutions resources
  simp only [subst] at related
  exact TypeRelated.literalSortCertificate formed related recipe.formed

theorem CanonicalDeltaElimination.normalizeSortReply
    (recipe : CanonicalDeltaElimination env U registry target strata source σ (.sort level)
      relevant profile footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.depth)
    (calls : recipe.Calls (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (destination : OriginalNestedDisplay U common expression assigned)
    (literal : destination.sourceExpression = .sort level)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight destination.graph destinationFrame.frame.raw)
    (closed : destinationAvailable.AtomClosed) (ordered : destination.sourceEnv.Ordered) :
    ∃ reply : SourceBoundedGeneratedQueryReply P base caps destination commonLeft commonRight profile
        (environmentCost (destinationFrame.frame.dependencyEnvironment ordered)),
      HEq reply.answer.reply.realization destinationFrame ∧
      ∀ policy, reply.answer.reply.query.observation.headDepth policy = 0 := by
  have related := recipe.interpret henv hscoped formed cutoff cutoffBound fuel constants
    callerSchedule bounded calls frame substitutions resources
  simp only [subst] at related
  exact TypeRelated.literalSortReply destination literal formed related recipe.formed
    destinationFrame generated closed ordered

end Lean4Lean.AnchoredSource.Adapted
