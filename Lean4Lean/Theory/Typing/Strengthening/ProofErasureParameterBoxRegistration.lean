import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePositiveHeaderRegistration

/-! # An actual registered parameter box

Install Box : Type -> Type and its constructor (A : Type) -> A -> Box A
through the source projection-registration judgment. This discharges the box
metadata hypotheses used by the projection replay test in a real extension.
-/
namespace Lean4Lean.VEnv.Strengthening.ParameterBoxRegistration
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The parameter box constructor retains one type parameter and one field. -/
def constructor (s c : Name) : VConstVal where
  name := c
  uvars := 0
  type := .forallE (.sort (.succ .zero))
    (.forallE (.bvar 0) (.app (.const s []) (.bvar 1)))

/-- The family has one type parameter and returns Type. -/
def family (s c : Name) : VInductiveType where
  name := s
  uvars := 0
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  numIndices := 0
  resultLevel := .succ .zero
  ctors := [constructor s c]

/-- A single nonrecursive parameter box declaration. -/
def declaration (s c : Name) : VInductDecl where
  uvars := 0
  nparams := 1
  types := [family s c]
  isUnsafe := false

/-- Registered metadata for the single-field box. -/
def info (s c : Name) : VProjectionInfo where
  uvars := 0
  nparams := 1
  nindices := 0
  resultLevel := .succ .zero
  ctorName := c
  ctorType := (constructor s c).type

/-- The raw result is Box applied to its parameter under the field binder. -/
theorem raw_shape : (declaration s c).RawCtorShape (family s c) (constructor s c) := by
  refine ⟨[.sort (.succ .zero), .bvar 0], .app (.const s []) (.bvar 1), rfl, by simp [declaration], ?_, rfl⟩
  exact ⟨family s c, by simp [declaration], .inr rfl, [], rfl, rfl, rfl, rfl⟩

/-- The real two-constant extension followed by projection registration is
well formed. No recursor or computational rule is assumed for the box. -/
theorem register_wf {base envT envC : VEnv}
    (hbase : base.WF) (hne : s ≠ c)
    (hT : base.addConstVals [(family s c).toVConstVal] = some envT)
    (hC : envT.addConstVals [constructor s c] = some envC) :
    (envC.addProjections [{ typeName := s, info := info s c }]).WF := by
  have HT : base.HasType 0 [] (family s c).type
      (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) := by
    change base.HasType 0 [] (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) _
    exact .forallE (.sort (by trivial)) (.sort (by trivial))
  have hctx : OnCtx [VExpr.sort (.succ .zero)] (base.IsType 0) :=
    ⟨trivial, _, HasType.sort (by trivial)⟩
  have hWT : envT.WF := hbase.addConstVals (by
    intro ci hci
    obtain rfl := List.mem_singleton.1 hci
    exact ⟨_, HT⟩) hT
  have hleT := VEnv.addConstVals_le hT
  have hc : envT.constants s = some (family s c).toVConstant :=
    VEnv.addConstVals_get hT (ci := (family s c).toVConstVal) (by simp)
  have hF : envT.HasType 0 [] (.const s [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := HasType.const0 hc ⟨_, HT.mono hleT⟩
  have hA : envT.HasType 0 [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hBA := HasType.app (hF.weak hWT) hA
  have hCtor : envT.HasType 0 [] (constructor s c).type
      (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) := by
    change envT.HasType 0 [] (.forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const s []) (.bvar 1)))) _
    exact .forallE (.sort (by trivial)) (.forallE hA (hBA.weak hWT))
  have hCtorWF : (constructor s c).toVConstant.WF envT := ⟨_, hCtor⟩
  have hWC : envC.WF := hWT.addConstVals (by
    intro ci hci
    obtain rfl := List.mem_singleton.1 hci
    exact hCtorWF) hC
  have hFamily : (declaration s c).TypeShape base [.sort (.succ .zero)] (family s c) := by
    refine ⟨_, [.sort (.succ .zero)], .sort (.succ .zero), [], .sort (.succ .zero),
      _, HT, rfl, rfl, IsDefEqCtx.refl hctx, ?_⟩
    exact HasType.sort (by trivial)
  have hParam : (declaration s c).CtorParameterShape envT [.sort (.succ .zero)] (constructor s c) :=
    ⟨[.sort (.succ .zero)], _, rfl, IsDefEqCtx.refl (hctx.mono (fun H => H.mono hleT))⟩
  have hparams : (declaration s c).SourceParameterWF base := by
    refine ⟨[.sort (.succ .zero)], envT, hT, ?_, ?_, ?_⟩
    · intro t ht
      obtain rfl := List.mem_singleton.1 ht
      exact hFamily
    · intro t ht k hk
      obtain rfl := List.mem_singleton.1 ht
      obtain rfl := List.mem_singleton.1 hk
      exact hParam
    · intro t ht k hk
      obtain rfl := List.mem_singleton.1 ht
      obtain rfl := List.mem_singleton.1 hk
      exact raw_shape
  apply WF.inductProjections (decl := declaration s c)
    (block := ⟨[(family s c).toVConstVal], [constructor s c], [], [],
      [{ typeName := s, info := info s c }]⟩) hbase hWC
  · simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, declaration, family, constructor] using hne
  · intro t ht
    obtain rfl := List.mem_singleton.1 ht
    exact ⟨_, HT⟩
  · intro k hk
    have hk' : k = constructor s c := by
      simpa [VInductDecl.constructorConstants, declaration, family] using hk
    subst k
    rfl
  · intro k hk
    have hk' : k = constructor s c := by
      simpa [VInductDecl.constructorConstants, declaration, family] using hk
    subst k
    exact hCtorWF
  · exact hparams
  · exact hparams.rawCtorShape
  · rfl
  · rfl
  · rfl
  · exact hT
  · exact hC

/-- Fresh family and constructor names permit the actual constant additions. -/
theorem exists_constants {base : VEnv}
    (hs : base.constants s = none) (hc : base.constants c = none) (hne : s ≠ c) :
    ∃ envT envC, base.addConstVals [(family s c).toVConstVal] = some envT ∧
      envT.addConstVals [constructor s c] = some envC := by
  let envT : VEnv := { base with constants := fun n => if s = n then some (family s c).toVConstant else base.constants n }
  have hT : base.addConstVals [(family s c).toVConstVal] = some envT := by
    simp [VEnv.addConstVals, VEnv.addConst, family, hs, envT]
    rfl
  have hc' : envT.constants c = none := by simp [envT, hne, hc]
  refine ⟨envT, { envT with constants := fun n => if c = n then some (constructor s c).toVConstant else envT.constants n }, hT, ?_⟩
  simp [VEnv.addConstVals, VEnv.addConst, constructor, hc']
  rfl

/-- A well-formed extension with actual box constants and projection metadata.
All old constants and registrations are preserved. -/
theorem exists_extension {base : VEnv} (hbase : base.WF)
    (hs : base.constants s = none) (hc : base.constants c = none) (hne : s ≠ c) :
    ∃ E : VEnv, E.WF ∧ base ≤ E ∧ E.projections s (info s c) ∧
      E.constants s = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ := by
  obtain ⟨envT, envC, hT, hC⟩ := exists_constants hs hc hne
  let entry : VProjectionEntry := { typeName := s, info := info s c }
  let E := envC.addProjections [entry]
  have hE : E.WF := register_wf hbase hne hT hC
  have htail : envT ≤ E := (VEnv.addConstVals_le hC).trans VEnv.addProjections_le
  exact ⟨E, hE, (VEnv.addConstVals_le hT).trans htail,
    VEnv.addProjections_iff.2 (.inl ⟨entry, by simp, rfl, rfl⟩),
    htail.constants (VEnv.addConstVals_get hT (ci := (family s c).toVConstVal) (by simp))⟩

end Lean4Lean.VEnv.Strengthening.ParameterBoxRegistration
