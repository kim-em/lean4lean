import Lean4Lean.Theory.Typing.AnchoredFamilyIntroduction
import Lean4Lean.Theory.Typing.AnchoredHeadBeta

/-! A terminal family demand observes the sort of its actually instantiated
assigned type. The declared telescope result need not itself be a sort. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The existing support observation provides the exact sort conversion used
to type the rigid head. No family interpretation or source-literal sort is an
input to this construction. -/
theorem Related.familyOfAssigned
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    {demand : FamilyData (Profile n)} {support : Profile (n+1)}
    (inert : CanonicalDataHead.HeadInert registry demand.name)
    (raw : env.IsDefEq U Γ (mkApps (.const demand.name demand.levels) lefts)
      (mkApps (.const demand.name demand.levels) rights) assigned)
    (typed : (Profile.singleton (n := n+1) (.family demand)).HasType support)
    (code : TypeRelated env U registry Γ assigned assigned support)
    (arguments : RankedData.Arguments env U (relations env U registry n) Γ demand.arguments lefts rights) :
    Related env U registry Γ (mkApps (.const demand.name demand.levels) lefts)
      (mkApps (.const demand.name demand.levels) rights) assigned
      (Profile.singleton (n := n+1) (.family demand)) support := by
  have member : (AtomData.sort demand.relevant : Atom (n+1)) ∈ support.atoms := by
    obtain ⟨cover, member, covered⟩ := typed.2.2 _ (List.mem_singleton_self _)
    cases cover with
    | sort flag =>
      change demand.relevant = flag at covered
      exact covered ▸ member
    | fn | pi | pad | family | ctor | record => contradiction
  have observed : SortRelated env U registry Γ assigned assigned demand.relevant := by
    have selected := code Γ .refl (.refl formed) (.sort demand.relevant)
      (by simpa only [Profile.rename_refl] using member)
    simpa only [lift'_refl, CodeAtom] using selected
  obtain ⟨_, _, level, _, ⟨exposure⟩, _, _, relevant⟩ := observed
  have atSort := exposure.sortPath henv
  exact Related.family henv hscoped typed code
    (RankedData.literalFamilyCodeOfInert henv hscoped inert (atSort.cast raw) relevant arguments)

end Lean4Lean.AnchoredSemantics
