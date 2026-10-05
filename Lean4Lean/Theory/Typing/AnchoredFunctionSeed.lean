import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain
import Lean4Lean.Theory.Typing.AnchoredSupport

/-! Recover a function key's actual self-admission in the caller's world,
even when its assigned raw type is not syntactically a Pi. The selected base
support is fixed before inspecting private displays. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false


theorem Related.fn_domain_self
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type (Profile.fn key output) typeProfile) :
    ∃ support : Profile n, key.input.HasType support ∧ support.HasType (.sort true) ∧
      TypeRelated env U registry Γ key.domain key.domain support := by
  have typed : (Profile.fn key output).HasType typeProfile := by
    have base := H (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
    simp only [lift'_refl, Profile.rename_refl] at base
    rcases base with empty | ⟨Δ, ρ, _, typed, _, _⟩
    · cases empty
    · exact Profile.rename_hasType_iff.mp typed
  have code := H.typeCode henv hscoped hΓ (by intro he; cases he)
  obtain ⟨prototypeA, prototypeB, domain, rows, result,
    member, _, _, inputTyped, row, _⟩ := typed.fn_inv (List.mem_singleton_self _)
  obtain ⟨support, basis⟩ := Basis.exists inputTyped
  have minimal := Basis.minimal basis
  obtain ⟨supportTyped, supportBound⟩ := Basis.valid basis
  have baseCode := code Γ .refl (.refl hΓ) (.pi prototypeA prototypeB domain rows)
    (by simpa only [Profile.rename_refl] using member)
  simp only [lift'_refl] at baseCode
  obtain ⟨display⟩ := baseCode
  obtain ⟨localSupport, localTyped, _, _, _, bridge⟩ := display.rowDomains key result row
  have focused := TypeRelated.focusMinimal henv (minimal.rename display.map)
    (Profile.rename_le_iff.mpr supportBound) (TypeRelated.left_diagonal display.domainRelated)
  have aligned := (focused.composeMinimal henv (minimal.rename display.map)
    localTyped (TypeRelated.symm henv localTyped.wf_type bridge)).symm henv
      ((Profile.rename_hasType_iff.mpr supportTyped).wf_type)
  have self := TypeRelated.left_diagonal aligned
  exact ⟨support, supportTyped, minimal.formation,
    (display.leftExposure.insertion henv).codeBack henv hscoped self⟩

theorem Related.fn_seed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type (Profile.fn key output) support) :
    Admitted env U registry Γ key key.anchor key.anchor := by
  obtain ⟨baseSupport, baseTyped, baseFormed, baseCode⟩ :=
    related.fn_domain_self henv hscoped hΓ
  have original := related (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at original
  rcases original with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn (key.rename ρ) (output.rename ρ))
      (List.mem_singleton_self _)
    obtain ⟨seed, _⟩ := behavior
    obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := seed
    have targetCode := baseCode.future henv insertion.toFuture
    have targetTyped := (Profile.rename_hasType_iff (ρ := ρ)).mpr baseTyped
    have changed := Related.retag henv targetTyped targetCode anchor
    have baseAnchor := Related.absorb henv insertion changed
    obtain ⟨embedding, embeddingMap⟩ := insertion.toEmbedding henv
    have baseRaw := raw.subst henv embedding.typed hΓ
    simp only [Key.rename, ← embeddingMap, embedding.leftInv] at baseRaw
    exact ⟨baseRaw, baseRaw, baseSupport, baseTyped, baseFormed, baseCode,
      baseAnchor, baseAnchor⟩

end Lean4Lean.AnchoredSemantics
