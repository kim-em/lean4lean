import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCertificateSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredNativeWitnessedReplay

/-! Replay the actual finite native capture instructions while retaining
certificates. In particular `commonPrefix` takes the stored argument tail;
it does not ask an unrestricted theorem to recreate a prefix frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem frame_environment_mpr
    {context : ContextDerivation sourceEnv U source}
    (same : locals = locals')
    (types : OriginalRichFrame sourceEnv env U registry target context locals σ τ available =
      OriginalRichFrame sourceEnv env U registry target context locals' σ τ available)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals' σ τ available)
    (ordered : sourceEnv.Ordered) :
    (types.mpr frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases same
  rfl

theorem NativeCertificateSpine.frame_environment
    (spine : NativeCertificateSpine env U registry target source σ τ available)
    (context : ContextDerivation sourceEnv U source) (ordered : sourceEnv.Ordered) :
    (spine.frame context).dependencyEnvironment ordered = context.dependencyClosures ordered := by
  induction spine with
  | nil => cases context; rfl
  | cons previous certificate resources typed arguments needs bounded covered ih =>
    cases context with
    | cons tail domain =>
      rw [NativeCertificateSpine.frame.eq_2]
      refine (frame_environment_mpr (by
        simp only [List.length_cons, List.range_succ_eq_map, Locals.push]) _ _ ordered).trans ?_
      simpa only [OriginalRichFrame.bind,
        OriginalRichFrame.dependencyEnvironment, RawOriginalRichFrame.dependencyEnvironment,
        ContextDerivation.dependencyClosures] using
        congrArg (fun previous => Closure.close (domain.dependencyOrigin ordered) previous :: previous)
          (ih tail)

private noncomputable def NativeCertificateSpine.leftWitness
    (spine : NativeCertificateSpine env U registry target source σ τ available) :
    NativeCertificateSpine env U registry target source σ σ available := by
  induction spine with
  | nil => exact .nil
  | cons previous certificate resources typed arguments needs bounded covered ih =>
    exact .cons ih certificate resources typed arguments.left_diagonal needs bounded covered

noncomputable def NativeSupportedReplay.certificateSpine
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    { _spine : NativeCertificateSpine env U registry target declared captures captures available //
      locals = List.range declared.length } := by
  induction replay with
  | nil => exact ⟨.nil, rfl⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have diagonal := argumentsSpine.leftWitness
    rw [source] at diagonal
    refine ⟨?_, rfl⟩
    have shift : Subst.lift_l (.skipN .refl later.length) arguments =
        fun i => arguments (i + later.length) := by
      funext i
      simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar]
    rw [shift]
    exact diagonal.drop later
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed
      needs bounded covered ih =>
    let entry := Classical.choose ((argumentsSpine.frame argumentContext).lookup_allDepth
      henv formed needed lookup)
    have related : Related env U registry target (arguments position) (arguments position)
        (domain.subst captures) input support :=
      alignment.related henv typed declaredCode entry.related.left_diagonal
    have certificate := domainCode
    rw [ih.property] at certificate
    refine ⟨.cons ih.val certificate resources typed related needs bounded covered, ?_⟩
    simp only [ih.property, List.length_cons, List.range_succ_eq_map, Locals.push]
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      needs n bounded empty ih =>
    have certificate : CodeCert env U registry target (List.range declared.length) captures domain
        (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
    have related : Related env U registry target witness witness (domain.subst captures)
        (Profile.empty (n := n)) .empty := by
      apply Related.of_singletons
      intro atom member
      cases member
    refine ⟨.cons ih.val certificate (fun _ _ h => nomatch h) (.empty .empty)
      related needs bounded (fun need hm atom ha => (empty need hm atom ha).elim), ?_⟩
    simp only [ih.property, List.length_cons, List.range_succ_eq_map, Locals.push]

/-- The same replay's finite output is realized at the actual equation
context, retaining its original domain references and raw substitution. -/
noncomputable def NativeSupportedReplay.originalFrame
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available)
    (context : ContextDerivation frameEnv U declared) :
    OriginalRichFrame frameEnv env U registry target context locals captures captures available := by
  let retained := NativeSupportedReplay.certificateSpine henv formed argumentContext argumentsSpine replay
  rw [retained.property]
  exact retained.val.frame context

theorem NativeSupportedReplay.originalFrame_environment
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available)
    (context : ContextDerivation frameEnv U declared) (ordered : frameEnv.Ordered) :
    (NativeSupportedReplay.originalFrame henv formed argumentContext argumentsSpine replay context).dependencyEnvironment ordered = context.dependencyClosures ordered := by
  unfold NativeSupportedReplay.originalFrame
  generalize NativeSupportedReplay.certificateSpine henv formed argumentContext argumentsSpine replay = retained
  rcases retained with ⟨spine, same⟩
  cases same
  exact spine.frame_environment context ordered

theorem NativeSupportedReplay.originalFrame_substitutions
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    Ctx.SubstEq env U target captures captures declared :=
  (replay.witnessed henv below formed argumentsRaw (argumentsSpine.fitsLeft henv formed)).1

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
