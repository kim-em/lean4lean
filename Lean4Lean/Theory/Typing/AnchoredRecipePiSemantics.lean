import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaCoherence
import Lean4Lean.Theory.Typing.AnchoredProfileUnrenaming

/-! Pure dependent Pi elimination and right-anchor admission. These proofs
use the actual paired Pi relation and binder resource; they make no original
fundamental or reindex calls. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- A selected row can be applied directly to a realized binder resource.
Its frozen domain is recovered from the actual Pi witness, so the binder's
stored support need not equal the row's domain support. -/
theorem TypeRelated.literalPiRowPairFromBinder
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (anchorEq : key.anchor = x)
    (raw : env.IsDefEq U target x y A)
    (argument : Related env U registry target x y A key.input support) :
    TypeRelated env U registry target (B.inst x) (D.inst y) result := by
  have base := whole target .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody ambient rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  obtain ⟨rowSupport, typed, rowFormed, _, path, code⟩ :=
    witness.rowDomains key result member
  change TypeRelated env U registry witness.context (key.domain.lift' witness.map)
    witness.leftDomain rowSupport at code
  have argument' := route.term henv argument
  have raw' := route.eq henv raw
  rw [← witness.leftExposure.literalPi_components.1] at argument' raw'
  have paired := Related.convert henv typed (code.symm henv typed.wf_type) argument'
  have pairedRaw := path.symm.cast raw'
  have admitted : Admitted env U registry witness.context (key.rename witness.map)
      (x.lift' witness.map) (y.lift' witness.map) := by
    refine ⟨?_, pairedRaw, rowSupport, typed, rowFormed, code.left_diagonal, ?_, paired⟩
    · simpa only [Key.rename, anchorEq, HasType] using pairedRaw.hasType.1
    · simpa only [Key.rename, anchorEq, Related] using paired.left_diagonal
  have bodies := witness.rowBodies key result member witness.context .refl
    (.refl (route.targetWF henv formed))
    (x.lift' witness.map) (y.lift' witness.map) (by
      simpa only [Lift.comp, Admitted] using admitted)
  apply route.codeBack henv hscoped
  simpa only [TypeRelated, Lift.comp, lift'_refl, Profile.rename_refl,
    lift'_depth_zero (l := Lift.refl.cons) rfl,
    witness.leftExposure.literalPi_components.2,
    witness.rightExposure.literalPi_components.2, lift'_inst_hi] using
      TypeRelated.trans henv bodies.2.2 bodies.2.1

theorem TypeRelated.literalPiRowFromBinder
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (anchorEq : key.anchor = x)
    (raw : env.IsDefEq U target x y A)
    (argument : Related env U registry target x y A key.input support) :
    TypeRelated env U registry target (B.inst x) (B.inst y) result :=
  whole.literalPiRowPairFromBinder henv hscoped formed member anchorEq raw argument

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.literalPiRightAdmissionFromBinder
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (anchorEq : key.anchor = x)
    (raw : env.IsDefEq U target x y A)
    (argument : Related env U registry target x y A key.input support) :
    Admitted env U registry target key y y := by
  have base := whole target .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody ambient rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  obtain ⟨rowSupport, typed, rowFormed, supportBound, path, code⟩ :=
    witness.rowDomains key result member
  change TypeRelated env U registry witness.context (key.domain.lift' witness.map)
    witness.leftDomain rowSupport at code
  obtain ⟨baseSupport, baseSupportEq, _⟩ := Profile.unrename_le supportBound
  have argument' := route.term henv argument
  rw [← witness.leftExposure.literalPi_components.1] at argument'
  have paired := Related.convert henv typed (code.symm henv typed.wf_type) argument'
  have basePath : TypeConversion env U target key.domain A := route.pathBack henv (by
    simpa only [witness.leftExposure.literalPi_components.1] using path)
  have pairedRaw := basePath.symm.cast raw
  have pairedBase : Related env U registry target x y key.domain key.input baseSupport :=
    route.termBack henv (by simpa only [baseSupportEq, Key.rename] using paired)
  have codeBase : TypeRelated env U registry target key.domain key.domain baseSupport :=
    route.codeBack henv hscoped (by simpa only [baseSupportEq] using code.left_diagonal)
  have typedBase : key.input.HasType baseSupport := (Profile.rename_hasType_iff (ρ := witness.map)).mp (by
    simpa only [Key.rename, baseSupportEq] using typed)
  have formedBase : baseSupport.HasType (.sort true) := (Profile.rename_hasType_iff (ρ := witness.map)).mp (by
    simpa only [baseSupportEq, Profile.rename_sort] using rowFormed)
  refine ⟨?_, ?_, baseSupport, typedBase, formedBase, codeBase, ?_, ?_⟩
  · simpa only [anchorEq] using pairedRaw
  · exact pairedRaw.hasType.2
  · simpa only [anchorEq, Related] using pairedBase
  · exact (pairedBase.symm henv).left_diagonal

end Lean4Lean.AnchoredSemantics
