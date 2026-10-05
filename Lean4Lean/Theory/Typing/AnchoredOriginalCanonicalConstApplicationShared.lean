import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstLegacyProducer
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeApplicationCompile

/-! The actual `constant #0` recipe branch returns ordinary shared code.
The function's canonical mask encloses only its closed original query; the
selected destination argument retains its exact local resource footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalConstSitePacket

theorem compileApplication
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (demand : RecipeVariableDemand env U registry target outerInput key.input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available demand.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output) arg.footprint,
      arg.footprint.Available available ∧
      ∀ policy, certificate.headDepth policy ≤
        max (policy packet.ownerName (packet.query.headDepth policy)) (arg.observation.headDepth policy) := by
  simpa only [List.nil_append, packet.observation_headDepth] using
    demand.compileApplication henv hscoped formed (domain := domain) (body := body) (result := result)
      hu hv (packet.observation function locals σ) (fun _ _ member => nomatch member)
      arg admitted sorted

end CanonicalConstSitePacket

/-- Both pieces come from the stored native row, not a requested output:
the actual legacy constant function and the selected variable's BinderPack. -/
theorem nativeLegacyConstantApplicationInputs {key : Key n} {output : Atom n} {σ : Subst}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (function : EndpointState owner.selected.origin.source U (D :: source)
      (.const name levels) (.forallE A B))
    (fn : SortableObs env U registry target (Locals.push locals) (σ.cons anchor)
      (.const name levels) (Profile.fn key output) fnFootprint)
    (arg : SortableObs env U registry target (Locals.push locals) (σ.cons anchor)
      (.bvar 0) rawInput argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (covered : packed.atoms ⊆ outerInput.atoms)
    (resources : outside.Available available) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output),
      ∃ demand : RecipeVariableDemand env U registry target outerInput key.input,
        packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
        ∀ policy, packet.query.headDepth policy = fn.headDepth policy := by
  obtain ⟨packet, nameEq, ownerEq, depth⟩ := canonicalConstSiteOfLegacy owner function fn
  obtain ⟨demand⟩ := SortableObs.recipeVariableArgumentDemand henv hscoped formed arg adapter
    pack covered resources
  exact ⟨packet, demand, nameEq, ownerEq, depth⟩

end Lean4Lean.AnchoredSource.Adapted
