import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredFunctionSeed

/-! A private assigned type need not descend to recover a base function key.
Only the finite value/type profiles are required to originate at the base. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false


theorem Related.fn_domain_self_inFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {key : Key n} {output : Atom n} {typeProfile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProofInsertion env U Γ Δ ρ)
    (H : Related env U registry Δ left right type
      (Profile.fn (key.rename ρ) (output.rename ρ)) (typeProfile.rename ρ)) :
    ∃ support : Profile n, key.input.HasType support ∧ support.HasType (.sort true) ∧
      TypeRelated env U registry Γ key.domain key.domain support := by
  have hΔ := frame.targetWF henv
  have typed : (Profile.fn key output).HasType typeProfile := by
    have base := H (.fn (key.rename ρ) (output.rename ρ))
      (List.mem_singleton_self _) Δ .refl (.refl hΔ)
    simp only [lift'_refl, Profile.rename_refl] at base
    rcases base with empty | ⟨Ω, τ, _, typed, _, _⟩
    · cases empty
    · have ht := Profile.rename_hasType_iff.mp typed
      exact Profile.rename_hasType_iff.mp ht
  have code := H.typeCode henv hscoped hΔ (by intro he; cases he)
  obtain ⟨prototypeA, prototypeB, domain, rows, result,
    member, _, _, inputTyped, row, _⟩ := typed.fn_inv (List.mem_singleton_self _)
  change Profile n at domain result
  change List (Key n × Profile n) at rows
  obtain ⟨support, basis⟩ := Basis.exists inputTyped
  have minimal := Basis.minimal basis
  obtain ⟨supportTyped, supportBound⟩ := Basis.valid basis
  have baseCode := code Δ .refl (.refl hΔ)
    (Atom.rename ρ (AtomData.pi prototypeA prototypeB domain rows : Atom (n + 1)))
    (by
      change _ ∈ ((typeProfile.rename ρ).rename .refl).atoms
      rw [Profile.rename_refl]
      exact List.mem_map_of_mem member)
  simp only [lift'_refl] at baseCode
  obtain ⟨display⟩ := baseCode
  have renamedRow : (key.rename ρ, result.rename ρ) ∈ Rows.rename ρ rows :=
    List.mem_map_of_mem row
  obtain ⟨localSupport, localTyped, _, _, _, bridge⟩ :=
    display.rowDomains (key.rename ρ) (result.rename ρ) renamedRow
  have focused := TypeRelated.focusMinimal henv ((minimal.rename ρ).rename display.map)
    (Profile.rename_le_iff.mpr (Profile.rename_le_iff.mpr supportBound))
    (TypeRelated.left_diagonal display.domainRelated)
  have aligned := (focused.composeMinimal henv ((minimal.rename ρ).rename display.map)
    localTyped (TypeRelated.symm henv localTyped.wf_type bridge)).symm henv
      ((Profile.rename_hasType_iff.mpr (Profile.rename_hasType_iff.mpr supportTyped)).wf_type)
  have self := TypeRelated.left_diagonal aligned
  have full := MixedInsertion.comp (.proof frame) (display.leftExposure.insertion henv)
  refine ⟨support, supportTyped, minimal.formation, ?_⟩
  apply full.codeBack henv hscoped
  simpa only [Key.rename, ← lift'_comp, ← Profile.rename_comp] using self

theorem Related.fn_seed_inFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : ProofInsertion env U Γ Δ ρ)
    (related : Related env U registry Δ left right type
      (Profile.fn (key.rename ρ) (output.rename ρ)) (support.rename ρ)) :
    Admitted env U registry Γ key key.anchor key.anchor := by
  obtain ⟨baseSupport, baseTyped, baseFormed, baseCode⟩ :=
    related.fn_domain_self_inFrame henv hscoped frame
  have original := related (.fn (key.rename ρ) (output.rename ρ))
    (List.mem_singleton_self _) Δ .refl (.refl (frame.targetWF henv))
  simp only [lift'_refl, Profile.rename_refl] at original
  rcases original with empty | ⟨Ω, τ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    obtain ⟨seed, _⟩ := behavior
    obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := seed
    have full := frame.comp insertion henv
    have targetCode := baseCode.future henv full.toFuture
    have targetTyped := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr baseTyped
    have changed := Related.retag henv targetTyped targetCode (by
      simpa only [Key.rename, ← lift'_comp, ← Profile.rename_comp, Related] using anchor)
    have baseAnchor := Related.absorb henv full changed
    obtain ⟨embedding, embeddingMap⟩ := full.toEmbedding henv
    have baseRaw := raw.subst henv embedding.typed frame.baseWF
    simp only [Key.rename, ← lift'_comp, ← embeddingMap, embedding.leftInv] at baseRaw
    exact ⟨baseRaw, baseRaw, baseSupport, baseTyped, baseFormed, baseCode,
      baseAnchor, baseAnchor⟩

end Lean4Lean.AnchoredSemantics
