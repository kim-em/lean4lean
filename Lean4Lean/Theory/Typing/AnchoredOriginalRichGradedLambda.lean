import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! Native rich lambda reconstruction retains exact original binder nodes.
Its finite pack is computed from returned body resources; generalized input
and output adaptation never manufactures an original endpoint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private raiseProfile_subset raiseKey_admitted append_available from
  Lean4Lean.Theory.Typing.AnchoredSortableGradedResult
set_option backward.isDefEq.respectTransparency false

structure RichGradedAtomResult (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned) (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  atom : Atom rank
  footprint : Footprint
  observation : RichObs sourceEnv env U registry Γ node locals σ (.singleton atom) footprint
  adapter : GeneralNormalAtomAdapter env U registry Γ atom (raiseAtom rank bound requested)
  resources : footprint.Available available
  live : Atom.Live env U registry Γ atom

theorem RichGradedResult.atom
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available (.singleton requested)) :
    Nonempty (RichGradedAtomResult sourceEnv env U registry Γ locals σ available node requested) := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, he⟩ := List.mem_map.mp member
  subst normal
  let selected := RichObs.select result.observation originalMember
  have observed := RichObs.view selected (AdapterNormal.view henv original)
  have finalAdapter : GeneralNormalAtomAdapter env U registry Γ (AdapterNormal.atom original)
      (raiseAtom result.rank result.bound requested) := by
    simpa only [GeneralNormalAtomAdapter, AdapterNormal.atom_idem] using entry
  exact ⟨{
    rank := result.rank
    bound := result.bound
    atom := AdapterNormal.atom original
    footprint := result.footprint
    observation := observed
    adapter := finalAdapter
    resources := result.resources
    live := (AdapterNormal.view henv original).live henv hscoped hΓ
      (result.live original originalMember) }⟩

theorem RichGradedResult.lam
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    {key : Key n} {output : Atom n} {support : Profile n}
    {domainNode : EndpointState sourceEnv U source annotation (.sort u)}
    {bodyNode : EndpointState sourceEnv U (annotation :: source) expression B}
    (codomain : EndpointState sourceEnv U (annotation :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert sourceEnv env U registry Γ domainNode locals σ true support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, List.Subset (need.atGrade n) key.input)
    (body : RichGradedResult sourceEnv env U registry Γ bodyNode (Locals.push locals) (σ.cons key.anchor)
      (Valuation.push localNeeds available) (.singleton output))
    (bodyClosed : (Valuation.push localNeeds available).AtomClosed) :
    Nonempty (RichGradedResult sourceEnv env U registry Γ (.lam hu hv domainNode codomain bodyNode) locals σ available (Profile.fn key output)) := by
  obtain ⟨selected⟩ := body.atom henv hscoped hΓ bodyClosed
  have raisedCovered : ∀ need ∈ localNeeds,
      List.Subset (need.atGrade selected.rank) (raiseProfile selected.rank selected.bound key.input) := by
    intro need member
    have hn := bounded need member
    have hN := Nat.le_trans hn selected.bound
    simp only [Need.atGrade, dif_pos hN]
    rw [← raiseProfile_trans hn selected.bound]
    exact raiseProfile_subset selected.bound (by
      have cover := covered need member
      simp only [Need.atGrade, dif_pos hn] at cover
      exact fun _ h => cover h)
  obtain ⟨packed, outside, normal, included, outsideAvailable⟩ :=
    Footprint.pack_available selected.resources
      (fun need member => Nat.le_trans (bounded need member) selected.bound)
      (fun need member atom ha => raisedCovered need member ha)
  have observed := RichObs.lam (codomain := codomain) hu hv (domain.raise selected.bound) (guard.raise henv selected.bound)
    selected.observation normal included
  have forward : GeneralNormalAtomAdapter env U registry Γ (n := selected.rank + 1)
      (AtomData.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (AtomData.fn (raiseKey selected.rank selected.bound key) (raiseAtom selected.rank selected.bound output)) :=
    .fn (.refl _) selected.adapter
  have backward := ((functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := Γ) selected.bound key output).inverse henv).toGeneralAdapter henv hscoped hΓ
  have adapter : GeneralNormalProfileAdapter env U registry Γ
      (Profile.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (raiseProfile (selected.rank + 1) (Nat.succ_le_succ selected.bound) (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) (GeneralAtomAdapter.comp forward backward) (.nil _)
  exact ⟨{
    rank := selected.rank + 1
    bound := Nat.succ_le_succ selected.bound
    raw := _
    footprint := _
    observation := observed
    adapter := adapter
    resources := append_available domainAvailable outsideAvailable
    live := Profile.Live.singleton_iff.mpr
      ⟨raiseKey_admitted selected.bound henv guard.anchor, selected.live⟩ }⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
