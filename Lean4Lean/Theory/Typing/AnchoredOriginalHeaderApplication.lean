import Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTailBudget

/-! A non-variable declared domain built by applying captured values. The
source certificate is reconstructed at the actual earlier declaration
occurrence, and target code follows from the function slot's real finite
capability and the stored application admission.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Reconstruct the application-shaped declared type `F x`, including when
`x` is a previously captured projection with a rich projected assigned type.
The key and admission are the finite original application query's payload;
no formation theorem for a synthesized source application is requested. -/
theorem HeaderValueAlignment.capturedApplication
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource (.app (.bvar functionIndex) (.bvar argumentIndex)) (.sort level))
    (owner : HeaderOwner field major)
    (value : RichBinderValue sourceEnv env U registry target owner.node
      ownerLocals ownerLeft ownerRight ownerAvailable (input : Profile n))
    (key : Key n) (output : Atom n)
    (supportEq : value.support = .singleton output)
    (functionNeed : Need.mk (n + 1) (Profile.fn key output) ∈ available functionIndex)
    (functionLookup : Lookup headerSource functionIndex (.forallE A (.sort level)))
    (rawInput : Profile n)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (argumentNeed : Need.mk n rawInput ∈ available argumentIndex)
    (admitted : Admitted env U registry target key (left argumentIndex) (left argumentIndex))
    (levelWF : level.WF U) (levelRelevant : Relevant level true)
    (same : owner.assigned.subst ownerLeft = .app (left functionIndex) (left argumentIndex)) :
    Nonempty (HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available input) := by
  have supportFormed : (Profile.singleton output).HasType (.sort true) :=
    supportEq ▸ value.certificate.formed
  obtain ⟨functionEntry⟩ := tail.lookup henv formed functionNeed functionLookup
  have functionValue : Related env U registry target (left functionIndex) (left functionIndex)
      (.forallE (A.subst left) (.sort level)) (Profile.fn key output) functionEntry.support := by
    simpa only [subst] using functionEntry.related.left_diagonal
  have resultCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n)
    henv levelWF levelWF rfl levelRelevant
  have resultValue := Related.apply (B := .sort level) (x := left argumentIndex)
    henv hscoped formed supportFormed resultCode functionValue admitted
  have result := resultValue.code_of_sortable henv hscoped formed supportFormed
  let certificate : RichCert headerEnv env U registry target (.ref domain) locals left true
      (.singleton output)
      ([(functionIndex, Need.mk (n + 1) (Profile.fn key output))] ++
        [(argumentIndex, Need.mk n rawInput)]) :=
    .legacy (.observe (.app (.legacy (.var locals left functionIndex _))
      (.legacy (.var locals left argumentIndex _)) arguments admitted) supportFormed)
  have resources : Footprint.Available
      ([(functionIndex, Need.mk (n + 1) (Profile.fn key output))] ++
        [(argumentIndex, Need.mk n rawInput)]) available := by
    intro index need member
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact functionNeed
    · cases List.mem_singleton.mp member
      exact argumentNeed
  have aligned : RichCodeTransferResult env U registry target owner.node.typeFormation.node (.ref domain)
      locals ownerLeft left available true value.support := by
    rw [supportEq]
    exact ⟨_, certificate, resources, by simpa only [same, subst] using result⟩
  exact ⟨{ value := value, aligned := aligned, path := by rw [same]; exact .refl }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
