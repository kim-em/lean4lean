import Lean4Lean.Theory.Typing.AnchoredGeneralFunctionAdapter

/-! Closed interpretation of hereditary adapters using only the final
assigned-type capability. Function arguments use the old anchor's actual
support; outputs use the final Pi row. Both calls decrease profile rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem profileMapWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (atomic : ∀ {Γ : List VExpr} {a b : Atom n},
      OnCtx Γ (env.IsType U) → GeneralAtomAdapter env U registry Γ a b → ∀ {l r A : VExpr} {old new : Profile n},
      (Profile.singleton b).HasType new → TypeRelated env U registry Γ A A new →
      Related env U registry Γ l r A (.singleton a) old →
      Related env U registry Γ l r A (.singleton b) new)
    {Γ : List VExpr} {p q : Profile n}
    (hΓ : OnCtx Γ (env.IsType U))
    (adapter : GeneralProfileAdapter env U registry Γ p q)
    {l r A : VExpr} {old new : Profile n}
    (typed : q.HasType new) (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A p old) :
    Related env U registry Γ l r A q new := by
  apply Related.of_singletons
  intro atom member
  obtain ⟨origin, originMember, ⟨entry⟩⟩ := adapter.origin member
  exact atomic hΓ entry (typed.singleton_of_mem member) code
    (related.singleton_of_mem originMember)

private theorem atomicMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped) :
    ∀ {Γ : List VExpr} {a b : Atom n},
      OnCtx Γ (env.IsType U) → GeneralAtomAdapter env U registry Γ a b → ∀ {l r A : VExpr} {old new : Profile n},
      (Profile.singleton b).HasType new → TypeRelated env U registry Γ A A new →
      Related env U registry Γ l r A (.singleton a) old →
      Related env U registry Γ l r A (.singleton b) new := by
  induction n with
  | zero =>
    intro Γ a b hΓ adapter l r A old new typed code related
    cases adapter with
    | refl => exact Related.retag henv typed code related
    | code action formed => exact action.termMapAt henv hscoped hΓ formed typed code related
  | succ n ih =>
    intro Γ a b hΓ adapter l r A old new typed code related
    cases adapter with
    | refl => exact Related.retag henv typed code related
    | code action formed => exact action.termMapAt henv hscoped hΓ formed typed code related
    | @fn _ key newKey output newOutput keys result =>
      intro requested member Δ ρ future
      cases List.mem_singleton.mp member
      have original := related (.fn key output) (List.mem_singleton_self _) Δ ρ future
      rcases original with hempty | ⟨Ω, τ, insertion, oldTyped, oldCode, values⟩
      · cases hempty
      · have full := future.comp insertion.toFuture henv
        have keys' := keys.future henv full
        have result' := result.future henv full
        have typed' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr typed
        have code' := code.future henv full
        simp only [lift'_comp, Profile.rename_comp, Key.rename_comp,
          Atom.rename_comp] at keys' result' typed' code'
        change (Profile.fn
          ((newKey.rename ρ).rename τ)
          ((newOutput.rename ρ).rename τ)).HasType ((new.rename ρ).rename τ) at typed'
        have behavior := values
          (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
          (List.mem_singleton_self _)
        have changed := FunctionBehavior.adaptGeneral henv hscoped ih (profileMapWith ih)
          keys' result' code' typed' behavior
        right
        refine ⟨Ω, τ, insertion, ?_, code', ?_⟩
        · simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Key.rename,
            inputKey] using typed'
        · intro atom hm
          cases List.mem_singleton.mp hm
          simpa only [TermAtom, Atom.rename_fn, inputKey, Key.rename] using changed
    | @pad _ a b adapter =>
      intro requested member Δ ρ future
      cases List.mem_singleton.mp member
      have original := related (.pad a) (List.mem_singleton_self _) Δ ρ future
      rcases original with hempty | ⟨Ω, τ, insertion, oldTyped, oldCode, values⟩
      · cases hempty
      · have full := future.comp insertion.toFuture henv
        have adapter' := adapter.future henv full
        have typed' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr typed
        have code' := code.future henv full
        simp only [lift'_comp, Profile.rename_comp, Atom.rename_comp] at adapter' typed' code'
        have lowerTyped : (Profile.singleton ((b.rename ρ).rename τ)).HasType
            ((new.rename ρ).rename τ).down :=
          Profile.HasType.pad_inv (by
            simpa only [Profile.rename_singleton, Atom.rename_pad, Profile.pad_singleton]
              using typed')
        have lower := values (.pad ((a.rename ρ).rename τ)) (List.mem_singleton_self _)
        have changed := ih (full.targetWF henv) adapter' lowerTyped (code'.down henv) lower
        right
        refine ⟨Ω, τ, insertion, ?_, code', ?_⟩
        · simpa only [Profile.rename_singleton, Atom.rename_pad] using typed'
        · intro atom hm
          cases List.mem_singleton.mp hm
          exact changed

theorem GeneralAtomAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {a b : Atom n}
    (adapter : GeneralAtomAdapter env U registry Γ a b) (henv : env.Ordered)
    (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : (Profile.singleton b).HasType new)
    (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A (.singleton a) old) :
    Related env U registry Γ l r A (.singleton b) new :=
  atomicMap henv hscoped hΓ adapter typed code related

theorem GeneralProfileAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {p q : Profile n}
    (adapter : GeneralProfileAdapter env U registry Γ p q) (henv : env.Ordered)
    (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : q.HasType new) (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A p old) :
    Related env U registry Γ l r A q new :=
  profileMapWith (atomicMap henv hscoped) hΓ adapter typed code related

theorem GeneralProfileAdapter.admissionMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {input : Profile n}
    (adapter : GeneralProfileAdapter env U registry Γ input key.input) (henv : env.Ordered)
    (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (admitted : Admitted env U registry Γ (inputKey key input) x y) :
    Admitted env U registry Γ key x y := by
  obtain ⟨_, _, support, typed, formed, code, _, _⟩ := seed
  obtain ⟨raw, pair, _, _, _, _, first, second⟩ := admitted
  exact ⟨raw, pair, support, typed, formed, code,
    adapter.termMap henv hscoped hΓ typed code first, adapter.termMap henv hscoped hΓ typed code second⟩

theorem GeneralKeyProgram.pull
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key newKey : Key n}
    (keys : GeneralKeyProgram env U registry Γ key newKey)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (admitted : Admitted env U registry Γ newKey x y) :
    Admitted env U registry Γ key x y :=
  keys.pullWith henv hscoped hΓ (fun adapter => adapter.termMap henv hscoped hΓ) seed admitted

end Lean4Lean.AnchoredSemantics
