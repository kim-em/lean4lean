import Lean4Lean.Theory.Typing.AnchoredLiteralPi
import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredProfileUnrenaming
import Lean4Lean.Theory.Typing.AnchoredDomainChain

/-! Row alignment is computed from the interpreted charged Pi. Unlike a
syntactic guard, this operation does not open or discard the code recipe. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.literalPiRowAlignment
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows) :
    Nonempty (DomainChain env U registry target key.input key.domain A) := by
  have base := whole target .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody ambient rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  obtain ⟨support, typed, supportFormed, bound, path, code⟩ :=
    witness.rowDomains key result member
  change TypeRelated env U registry witness.context (key.domain.lift' witness.map)
    witness.leftDomain support at code
  obtain ⟨originalSupport, supportEq, _⟩ := Profile.unrename_le bound
  have raw : TypeConversion env U target key.domain A := route.pathBack henv (by
    simpa only [witness.leftExposure.literalPi_components.1] using path)
  have related : TypeRelated env U registry target key.domain A originalSupport :=
    route.codeBack henv hscoped (by
      simpa only [supportEq, witness.leftExposure.literalPi_components.1] using code)
  have originalTyped : key.input.HasType originalSupport :=
    (Profile.rename_hasType_iff (ρ := witness.map)).mp (by
      simpa only [Key.rename, supportEq] using typed)
  have originalFormed : originalSupport.HasType (.sort true) :=
    (Profile.rename_hasType_iff (ρ := witness.map)).mp (by
      simpa only [supportEq, Profile.rename_sort] using supportFormed)
  exact ⟨.step raw originalTyped originalFormed related (.refl _)⟩

end Lean4Lean.AnchoredSemantics
