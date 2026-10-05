import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureGeneration

/-! Concrete realization producers for generated common scope. They preserve
actual source frames and their computed closure environments. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Package the same constructed frame using the full substitution equations
already proved by generation. This introduces no semantic retyping. -/
theorem ScopedCaptureGenerated.realize
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ result : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available,
      ScopedCaptureGenerated base commonLeft commonRight graph result.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        result.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  obtain ⟨left, right⟩ := generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, fun _ => rfl⟩

/-- Enter a fresh common source binder using the actual independent original
domain and rich source frame on this side. The displayed annotation need
not have an original proof in any common source environment. -/
theorem OriginalCaptureRealization.bindGenerated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail.frame.raw)
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
      ScopedCaptureGenerated base (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed) next.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered =
          .close (domain.dependencyOrigin ordered) (tail.frame.dependencyEnvironment ordered) ::
            tail.frame.dependencyEnvironment ordered := by
  let next := tail.frame.bind domain certificate resources typed arguments needs bounded covered
  have nextGenerated : ScopedCaptureGenerated base (commonLeft.cons x) (commonRight.cons y)
      (.bind graph domain annotation displayed) next.raw :=
    .bind generated domain annotation displayed certificate resources typed arguments needs bounded covered
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons x) ((raw.comp commonRight).cons y) (A :: source) :=
    .cons tail.substitutions (domain.sound.defeq.mono sourceBelow) rawArguments
  obtain ⟨result, resultGenerated, same⟩ := nextGenerated.realize next substitutions
  exact ⟨result, resultGenerated, same⟩

/-- Source weakening below a fresh common binder preserves the exact source
frame, including every original captured owner. -/
theorem OriginalCaptureRealization.weakenGenerated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (previous : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph previous.frame.raw)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight) :
    ∃ result : OriginalCaptureRealization (.weaken graph insertion) env registry target
        locals nextLeft nextRight available,
      ScopedCaptureGenerated base nextLeft nextRight (.weaken graph insertion) result.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        result.frame.dependencyEnvironment ordered = previous.frame.dependencyEnvironment ordered :=
  (ScopedCaptureGenerated.weaken generated insertion leftTail rightTail).realize
    previous.frame previous.substitutions

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
