import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPriorRawBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionPriorFieldSupport
import Lean4Lean.Theory.Typing.AnchoredProjectionSortableOutput

/-! The original application supplies its own key anchor. Projected value
code and the independently funded raw projection equality extend that exact
admission; a retained record request's domain or anchor is never substituted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Pull the original application's admission through the same function
factor used to obtain its assigned-domain support. -/
theorem RichFunctionDemandFactor.admission
    {key : Key n} {output : Atom n}
    (factor : RichFunctionDemandFactor sourceEnv env U registry target node locals σ available key output)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (original : Admitted env U registry target key left right) :
    Admitted env U registry target factor.key left right := by
  have live := (Profile.Live.singleton_iff.mp factor.live).1
  exact factor.keys.pull henv hscoped formed live
    (AdapterNormal.normalizeAdmission henv hscoped formed
      (original.raiseFamily henv factor.bound))

/-- Reattach sortable value code to the original key's actual support. Raw
typing remains a separate input obtained from the original projection rule. -/
theorem priorSortableKeyAdmissions
    {key : Key n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : Admitted env U registry target key left left)
    (sortable : key.input.HasType (.sort relevant))
    (values : TypeRelated env U registry target left right key.input)
    (raw : env.IsDefEq U target left right fieldType)
    (path : TypeConversion env U target key.domain fieldType) :
    Admitted env U registry target key left right ∧
      Admitted env U registry target key right right := by
  obtain ⟨anchorRaw, _, support, typed, supported, code, anchor, _⟩ := original
  have pair := Related.of_sortable_code henv sortable typed values code
  have pairRaw := path.symm.cast raw
  have rightAnchor := Related.trans henv hscoped anchor pair
  exact ⟨⟨anchorRaw, pairRaw, support, typed, supported, code, anchor, pair⟩,
    ⟨anchorRaw.trans pairRaw, pairRaw.hasType.2, support, typed, supported, code,
      rightAnchor, (Related.symm henv rightAnchor).left_diagonal⟩⟩

/-- The same selected function factor retains the original key admission,
then consumes the actual prior-field path and projected raw/code pairs. -/
theorem RichFunctionDemandFactor.priorSortableAdmissions
    {key : Key n} {output : Atom n}
    (factor : RichFunctionDemandFactor sourceEnv env U registry target node locals σ available key output)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (original : Admitted env U registry target key left left)
    (sortable : factor.key.input.HasType (.sort relevant))
    (values : TypeRelated env U registry target left right factor.key.input)
    (raw : env.IsDefEq U target left right fieldType)
    (path : TypeConversion env U target factor.key.domain fieldType) :
    Admitted env U registry target factor.key left right ∧
      Admitted env U registry target factor.key right right :=
  priorSortableKeyAdmissions henv hscoped (factor.admission henv hscoped formed original)
    sortable values raw path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
