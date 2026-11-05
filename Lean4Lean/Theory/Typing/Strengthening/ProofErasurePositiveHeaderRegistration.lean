import Lean4Lean.Theory.Typing.PrefixUnfolding.NormalCongruence
import Lean4Lean.Theory.Typing.EtaOpening

/-! # Registering a positive phantom family

The positive, field-free family retains its parameters. The actual
projection-stage environment judgment accepts a family header
ordinarily equal to the constructor's parameter telescope. No directed erased
computation is required for this installation.
-/
namespace Lean4Lean.VEnv.Strengthening.PositiveHeaderRegistration
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

def constructor (U : Nat) (ps : List VExpr) (s c : Name) : VConstVal where
  name := c
  uvars := U
  type := VExpr.wrapForalls ps (etaOpen ps.length (.const s (VLevel.params U)))

def family (U : Nat) (ps : List VExpr) (T : VExpr) (s c : Name) : VInductiveType where
  name := s
  uvars := U
  type := T
  numIndices := 0
  resultLevel := .succ .zero
  ctors := [constructor U ps s c]

def declaration (U : Nat) (ps : List VExpr) (T : VExpr) (s c : Name) : VInductDecl where
  uvars := U
  nparams := ps.length
  types := [family U ps T s c]
  isUnsafe := false

def info (U : Nat) (ps : List VExpr) (s c : Name) : VProjectionInfo where
  uvars := U
  nparams := ps.length
  nindices := 0
  resultLevel := .succ .zero
  ctorName := c
  ctorType := (constructor U ps s c).type

/-- The constructor's raw result uses exactly the literal parameter variables,
with no fields, indices, recursive arguments, or recursor assumptions. -/
theorem raw_shape : (declaration U ps T s c).RawCtorShape (family U ps T s c)
    (constructor U ps s c) := by
  let result := etaOpen ps.length (VExpr.const s (VLevel.params U))
  have E : result = VExpr.mkApps (.const s (VLevel.params U))
      ((declaration U ps T s c).paramVars 0) := by
    simp only [result, etaOpen_spine, VExpr.liftN, InductiveSignature.vars,
      VInductDecl.paramVars, declaration]
  have EG : result.getAppFnArgs =
      (.const s (VLevel.params U), (declaration U ps T s c).paramVars 0) := by
    simp only [E, VExpr.getAppFnArgs, VExpr.getAppFnArgs_go_mkApps,
      List.append_nil, VExpr.getAppFnArgs.go]
  refine ⟨ps, result, rfl, Nat.le_refl _, ?_, ?_⟩
  · change (declaration U ps T s c).RawIndAppAt (some s) (ps.length - ps.length) result
    unfold VInductDecl.RawIndAppAt
    change ∃ t ∈ (declaration U ps T s c).types, _
    change ∃ t ∈ (declaration U ps T s c).types,
      (some s = none ∨ some s = some t.name) ∧ ∃ levels,
      result.getAppFnArgs.1 = .const t.name levels ∧ levels.length = U ∧
      result.getAppFnArgs.2.length = ps.length + t.numIndices ∧
      result.getAppFnArgs.2.take ps.length = (declaration U ps T s c).paramVars (ps.length - ps.length)
    rw [EG]
    refine ⟨family U ps T s c, by simp [declaration], .inr rfl, VLevel.params U, rfl,
      VLevel.params_length, ?_, ?_⟩
    · simp [VInductDecl.paramVars, declaration, family]
    · simp only [Nat.sub_self]
      apply List.take_of_length_le
      simp [VInductDecl.paramVars, declaration]
  · change result.getAppFnArgs.1 = .const s (VLevel.params U)
    rw [EG]

/-- Installing the two constants and their actual projection metadata is
well formed whenever the stored family header is ordinarily equal to the
chosen parameter header. This uses `WF.inductProjections` directly, so it
constructs a real registered prefix, not free-standing metadata. -/
theorem register_wf {base envT envC : VEnv}
    (hbase : base.WF) (hne : s ≠ c)
    (HE : ∃ v, base.IsDefEq U [] T (VExpr.wrapForalls ps (.sort (.succ .zero))) (.sort v))
    (hT : base.addConstVals [(family U ps T s c).toVConstVal] = some envT)
    (hC : envT.addConstVals [constructor U ps s c] = some envC) :
    (envC.addProjections [{ typeName := s, info := info U ps s c }]).WF := by
  have HT : base.IsType U [] T := ⟨_, HE.choose_spec.hasType.1⟩
  have HT' : base.IsType U [] (VExpr.wrapForalls ps (.sort (.succ .zero))) :=
    ⟨_, HE.choose_spec.hasType.2⟩
  have hctx : OnCtx ps.reverse (base.IsType U) := by
    simpa only [List.append_nil] using (IsType.wrapForalls_inv hbase (by trivial) HT').1
  have hWT : envT.WF := hbase.addConstVals (by
    intro ci hci
    obtain rfl := List.mem_singleton.1 hci
    exact HT) hT
  have hleT := VEnv.addConstVals_le hT
  have hc : envT.constants s = some (family U ps T s c).toVConstant :=
    VEnv.addConstVals_get hT (ci := (family U ps T s c).toVConstVal) (by simp)
  have hf : envT.HasType U [] (.const s (VLevel.params U))
      (VExpr.wrapForalls ps (.sort (.succ .zero))) :=
    (HasType.const0 hc (HT.mono hleT)).defeqU_r hWT (by trivial) (HE.choose_spec.toU.mono hleT)
  have hOpen := hf.etaOpen_wf hWT.ordered (by trivial)
  obtain ⟨v, hCtor⟩ := VExpr.wrapForalls_defeq hOpen.1 hOpen.2
  have hCtorWF : (constructor U ps s c).toVConstant.WF envT := ⟨v, hCtor⟩
  have hWC := hWT.addConstVals (by
    intro ci hci
    obtain rfl := List.mem_singleton.1 hci
    exact hCtorWF) hC
  have hFamily : (declaration U ps T s c).TypeShape base ps (family U ps T s c) := by
    obtain ⟨v, HE⟩ := HE
    refine ⟨VExpr.wrapForalls ps (.sort (.succ .zero)), ps, .sort (.succ .zero), [], .sort (.succ .zero), .sort v,
      HE, VExpr.takeForalls_wrapForalls ps _, rfl, IsDefEqCtx.refl hctx, ?_⟩
    exact HasType.sort (by trivial)
  have hCtor : (declaration U ps T s c).CtorParameterShape envT ps (constructor U ps s c) :=
    ⟨ps, _, VExpr.takeForalls_wrapForalls ps _, IsDefEqCtx.refl (hctx.mono (fun H => H.mono hleT))⟩
  have hparams : (declaration U ps T s c).SourceParameterWF base := by
    refine ⟨ps, envT, hT, ?_, ?_, ?_⟩
    · intro t ht
      obtain rfl := List.mem_singleton.1 ht
      exact hFamily
    · intro t ht k hk
      obtain rfl := List.mem_singleton.1 ht
      obtain rfl := List.mem_singleton.1 hk
      exact hCtor
    · intro t ht k hk
      obtain rfl := List.mem_singleton.1 ht
      obtain rfl := List.mem_singleton.1 hk
      exact raw_shape
  apply WF.inductProjections (decl := declaration U ps T s c)
    (block := ⟨[(family U ps T s c).toVConstVal], [constructor U ps s c], [], [],
      [{ typeName := s, info := info U ps s c }]⟩) hbase hWC
  · simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, declaration, family, constructor] using hne
  · intro t ht
    obtain rfl := List.mem_singleton.1 ht
    exact HT
  · intro k hk
    have hk' : k = constructor U ps s c := by
      simpa [VInductDecl.constructorConstants, declaration, family] using hk
    subst k
    rfl
  · intro k hk
    have hk' : k = constructor U ps s c := by
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

/-- Fresh names suffice to perform the actual two constant additions. -/
theorem exists_constants {base : VEnv}
    (hs : base.constants s = none) (hc : base.constants c = none) (hne : s ≠ c) :
    ∃ envT envC,
      base.addConstVals [(family U ps T s c).toVConstVal] = some envT ∧
      envT.addConstVals [constructor U ps s c] = some envC := by
  let envT : VEnv := { base with constants := fun n => if s = n then some (family U ps T s c).toVConstant else base.constants n }
  have hT : base.addConstVals [(family U ps T s c).toVConstVal] = some envT := by
    simp [VEnv.addConstVals, VEnv.addConst, family, hs, envT]
    rfl
  have hc' : envT.constants c = none := by simp [envT, hne, hc]
  refine ⟨envT, { envT with constants := fun n => if c = n then some (constructor U ps s c).toVConstant else envT.constants n }, hT, ?_⟩
  simp [VEnv.addConstVals, VEnv.addConst, constructor, hc']
  rfl

end Lean4Lean.VEnv.Strengthening.PositiveHeaderRegistration
