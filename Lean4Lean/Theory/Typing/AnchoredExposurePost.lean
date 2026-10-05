import Lean4Lean.Theory.Typing.AnchoredSemantics

/-! Append concrete typed world routes to an exposure's final context. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv

noncomputable def Exposure.postInsertion
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {expression head : VExpr} {ρ i : Lift}
    (E : Exposure env U registry Γ expression Δ ρ head)
    (henv : env.Ordered) (I : ProofInsertion env U Δ Ω i) :
    Exposure env U registry Γ expression Ω (ρ.comp i) (head.lift' i) := by
  let pulled := E.terminal.pullProof henv I
  let target := Classical.choose pulled
  let data := Classical.choose_spec pulled
  exact {
    added := E.added
    result := E.result
    postMap := E.postMap.comp i
    postContext := target
    trace := E.trace
    generated := E.generated
    post := E.post.comp data.1 henv
    terminal := data.2
    map_eq := by rw [← Lift.comp_assoc, E.map_eq]
    result_eq := by rw [lift'_comp, E.result_eq]
    sound := by simpa only [lift'_comp] using E.sound.weak' henv I.weakening
    headType := by
      obtain ⟨u, hu⟩ := E.headType
      exact ⟨u, by simpa only [lift'] using hu.weak' henv I.weakening⟩ }

def Exposure.postContextChange (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head)
    (chain : ContextChain env U Δ Ω) : Exposure env U registry Γ expression Ω ρ head :=
  { E with
    terminal := E.terminal.trans chain
    sound := chain.path henv E.sound
    headType := chain.isType henv E.headType }

theorem Exposure.postMixed_exists (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head)
    (path : MixedInsertion env U Δ Ω τ) :
    Nonempty (Exposure env U registry Γ expression Ω (ρ.comp τ) (head.lift' τ)) := by
  induction path generalizing ρ head with
  | proof insertion => exact ⟨E.postInsertion henv insertion⟩
  | context chain => simpa only [Lift.comp, lift'_refl] using
      (show Nonempty _ from ⟨E.postContextChange henv chain⟩)
  | comp _ _ first second =>
    obtain ⟨middle⟩ := first E
    obtain ⟨result⟩ := second middle
    simpa only [Lift.comp_assoc, lift'_comp] using (show Nonempty _ from ⟨result⟩)

noncomputable def Exposure.postMixed (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head)
    (path : MixedInsertion env U Δ Ω τ) :
    Exposure env U registry Γ expression Ω (ρ.comp τ) (head.lift' τ) :=
  Classical.choice (E.postMixed_exists henv path)

end Lean4Lean.AnchoredSemantics
