import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem TrEnv.exists_addConst (H : TrEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) : ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci =>
    exfalso
    obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩
    rw [hn] at hci
    contradiction

/-- Any production `Eq` inductive visible in a translated environment is the
canonical abstract equality constant. This replaces the former, vacuous claim
that translated environments contained no inductives at all. -/
theorem TrEnv'.eq_quotReady (H : TrEnv' .unsafe C Q venv)
    (heq : C.find? ``Eq = some (.inductInfo info)) : venv.QuotReady := by
  induction H with
  | empty => simp [SMap.find?] at heq
  | ignore hn hhidden H ih =>
    exact False.elim <| hhidden DefinitionSafety.unsafe_le
  | «axiom» htr hn hwf hadd H ih =>
    rw [H.map_wf.find?_insert] at heq
    split at heq
    · simp at heq
    · exact (VEnv.addConst_le hadd).constants (ih heq)
  | defn htr hn hwf hadd H ih =>
    rw [H.map_wf.find?_insert] at heq
    split at heq
    · simp at heq
    · exact (VEnv.addConst_le hadd).constants (ih heq)
  | thm htr hn hwf hprop hadd H ih =>
    rw [H.map_wf.find?_insert] at heq
    split at heq
    · simp at heq
    · exact (VEnv.addConst_le hadd).constants (ih heq)
  | «opaque» htr hn hwf hadd H ih =>
    rw [H.map_wf.find?_insert] at heq
    split at heq
    · simp at heq
    · exact (VEnv.addConst_le hadd).constants (ih heq)
  | quot hready hadd H ih =>
    exact hadd.le.constants hready
  | induct _ hadd _ _ =>
    cases hadd with
    | intro _ _ _ _ _ _ _ heqReady => exact heqReady _ heq

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁') (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  constructor
  · intro n a ha
    simp at ha ⊢
    split at ha <;> split <;> simp_all
    exact H.constants ha
  · exact H.defeqs

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df := by
  constructor
  · exact H.constants
  · rintro d (rfl | hd)
    · exact .inl rfl
    · exact .inr (H.defeqs hd)

theorem VEnv.addConsts_mono {env₁ env₂ env₁' env₂' : VEnv}
    {cis : List VConstVal}
    (H : env₁ ≤ env₂)
    (h₁ : env₁.addConsts cis = some env₁')
    (h₂ : env₂.addConsts cis = some env₂') :
    env₁' ≤ env₂' := by
  induction cis generalizing env₁ env₂ env₁' env₂' with
  | nil =>
    simp [VEnv.addConsts] at h₁ h₂
    subst env₁'
    subst env₂'
    exact H
  | cons ci constants ih =>
    simp only [VEnv.addConsts] at h₁ h₂
    cases hhead₁ : env₁.addConst ci.name ci.toVConstant with
    | none => simp [hhead₁] at h₁
    | some middle₁ =>
      cases hhead₂ : env₂.addConst ci.name ci.toVConstant with
      | none => simp [hhead₂] at h₂
      | some middle₂ =>
        rw [hhead₁] at h₁
        rw [hhead₂] at h₂
        exact ih (VEnv.addConst_mono H hhead₁ hhead₂) h₁ h₂

theorem VEnv.addDefEqs_mono {env₁ env₂ : VEnv} {dfs : List VDefEq}
    (H : env₁ ≤ env₂) :
    env₁.addDefEqs dfs ≤ env₂.addDefEqs dfs := by
  induction dfs generalizing env₁ env₂ with
  | nil => exact H
  | cons rule rules ih => exact ih (VEnv.addDefEq_mono H)

theorem VInductBlock.install_mono
    (H : env₁ ≤ env₂)
    (h₁ : VInductBlock.install env₁ block = some env₁')
    (h₂ : VInductBlock.install env₂ block = some env₂') :
    env₁' ≤ env₂' := by
  unfold VInductBlock.install at h₁ h₂
  cases htypes₁ : env₁.addConsts block.types with
  | none => simp [htypes₁] at h₁
  | some types₁ =>
    cases htypes₂ : env₂.addConsts block.types with
    | none => simp [htypes₂] at h₂
    | some types₂ =>
      cases hctors₁ : types₁.addConsts block.ctors with
      | none => simp [htypes₁, hctors₁] at h₁
      | some ctors₁ =>
        cases hctors₂ : types₂.addConsts block.ctors with
        | none => simp [htypes₂, hctors₂] at h₂
        | some ctors₂ =>
          cases hrecs₁ : ctors₁.addConsts block.recursors with
          | none => simp [htypes₁, hctors₁, hrecs₁] at h₁
          | some recs₁ =>
            cases hrecs₂ : ctors₂.addConsts block.recursors with
            | none => simp [htypes₂, hctors₂, hrecs₂] at h₂
            | some recs₂ =>
              simp [htypes₁, hctors₁, hrecs₁] at h₁
              simp [htypes₂, hctors₂, hrecs₂] at h₂
              subst env₁'
              subst env₂'
              apply VEnv.addDefEqs_mono
              apply VEnv.addConsts_mono
                (cis := block.recursors) _ hrecs₁ hrecs₂
              apply VEnv.addConsts_mono
                (cis := block.ctors) _ hctors₁ hctors₂
              exact VEnv.addConsts_mono H htypes₁ htypes₂

theorem VEnv.addConst_eq_of_ne
    {env env' : VEnv}
    (hadd : env.addConst name ci = some env') (hne : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  simp [hne]

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} (H : env.HasPrimitives)
    (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') : env'.HasPrimitives := by
  have le := VEnv.addConst_le hadd
  have same (n : Name) (hp : Environment.primitives.contains n = true) :
      env'.constants n = env.constants n :=
    VEnv.addConst_eq_of_ne hadd fun h => by subst h; simp_all
  have oldContains (n : Name) (hp : Environment.primitives.contains n = true) :
      env'.contains n → env.contains n := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, (same n hp) ▸ hci⟩
  have newContains (n : Name) : env.contains n → env'.contains n := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, le.constants hci⟩
  let prims := [
    ``Bool, ``Bool.false, ``Bool.true,
    ``Nat, ``Nat.zero, ``Nat.succ,
    ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
    ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
    ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
    ``Nat.shiftLeft, ``Nat.shiftRight,
    ``String.ofList, ``Char.ofNat]
  have hprims : Environment.primitives = .ofList prims := rfl
  replace hprims {n} : Environment.primitives.contains n ↔ n ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  have primBool : Environment.primitives.contains ``Bool = true := hprims.2 (by simp [prims])
  have primBoolFalse : Environment.primitives.contains ``Bool.false = true :=
    hprims.2 (by simp [prims])
  have primBoolTrue : Environment.primitives.contains ``Bool.true = true :=
    hprims.2 (by simp [prims])
  have primNat : Environment.primitives.contains ``Nat = true := hprims.2 (by simp [prims])
  have primNatZero : Environment.primitives.contains ``Nat.zero = true :=
    hprims.2 (by simp [prims])
  have primNatSucc : Environment.primitives.contains ``Nat.succ = true :=
    hprims.2 (by simp [prims])
  have prim (n : Name) (h : n ∈ [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
      ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
      ``Nat.shiftLeft, ``Nat.shiftRight, ``Char.ofNat, ``String.ofList]) :
      Environment.primitives.contains n = true := by
    simp at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> exact hprims.2 (by simp [prims])
  constructor
  · intro h
    let ⟨h1, h2⟩ := H.bool (oldContains _ primBool h)
    exact ⟨newContains _ h1, newContains _ h2⟩
  · intro ci h; apply H.boolFalse; rwa [← same _ primBoolFalse]
  · intro ci h; apply H.boolTrue; rwa [← same _ primBoolTrue]
  · intro h
    let ⟨h1, h2⟩ := H.nat (oldContains _ primNat h)
    exact ⟨newContains _ h1, newContains _ h2⟩
  · intro ci h; apply H.natZero; rwa [← same _ primNatZero]
  · intro ci h; apply H.natSucc; rwa [← same _ primNatSucc]
  · intro h a b; exact (H.natAdd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natSub (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMul (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natPow (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natGcd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMod (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natDiv (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBEq (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBLE (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLAnd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLOr (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natXor (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftLeft (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftRight (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro ci h; apply H.charOfNat; rwa [← same _ (prim _ (by simp))]
  · intro ci h
    obtain ⟨rfl, h2, h3⟩ := H.stringOfList (by rwa [← same _ (prim _ (by simp))])
    exact ⟨rfl, h2.mono le, h3.mono le⟩

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} (H : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives :=
  { H with
    natAdd := fun h a b => (H.natAdd h a b).mono VEnv.addDefEq_le
    natSub := fun h a b => (H.natSub h a b).mono VEnv.addDefEq_le
    natMul := fun h a b => (H.natMul h a b).mono VEnv.addDefEq_le
    natPow := fun h a b => (H.natPow h a b).mono VEnv.addDefEq_le
    natGcd := fun h a b => (H.natGcd h a b).mono VEnv.addDefEq_le
    natMod := fun h a b => (H.natMod h a b).mono VEnv.addDefEq_le
    natDiv := fun h a b => (H.natDiv h a b).mono VEnv.addDefEq_le
    natBEq := fun h a b => (H.natBEq h a b).mono VEnv.addDefEq_le
    natBLE := fun h a b => (H.natBLE h a b).mono VEnv.addDefEq_le
    natLAnd := fun h a b => (H.natLAnd h a b).mono VEnv.addDefEq_le
    natLOr := fun h a b => (H.natLOr h a b).mono VEnv.addDefEq_le
    natXor := fun h a b => (H.natXor h a b).mono VEnv.addDefEq_le
    natShiftLeft := fun h a b => (H.natShiftLeft h a b).mono VEnv.addDefEq_le
    natShiftRight := fun h a b => (H.natShiftRight h a b).mono VEnv.addDefEq_le
    stringOfList := fun h =>
      let ⟨h1, h2, h3⟩ := H.stringOfList h
      ⟨h1, h2.mono VEnv.addDefEq_le, h3.mono VEnv.addDefEq_le⟩ }

theorem VEnvs.WF.safePrimitives_add {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = []) :
    (env.add ci).find? (n : Name) = some (ci' : ConstantInfo) → Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hp
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = some ci' at hfind
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert] at hfind
  split at hfind
  · cases hfind
    rename_i heq
    have heq' := LawfulBEq.eq_of_beq heq
    cases heq'
    exact hok hp
  · apply wf.safePrimitives ?_ hp
    rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
    exact hfind

/-- Extend only the unsafe abstract model.  This is the safety-indexed shape
of an unsafe inductive declaration: the production map changes for every
checker view, but partial and safe views justify that change through
`TrEnv'.ignore`, while the unsafe view receives the abstract block. -/
theorem VEnvs.WF.extendUnsafe
    {ves : VEnvs} {env env' : Environment} (wf : ves.WF env)
    (unsafeEnv : VEnv)
    (htrUnsafe : TrEnv' .unsafe env'.constants env'.quotInit unsafeEnv)
    (htrPartial : TrEnv' .partial env'.constants env'.quotInit
      (ves.venv .partial))
    (htrSafe : TrEnv' .safe env'.constants env'.quotInit
      (ves.venv .safe))
    (hunsafePrimitives : unsafeEnv.HasPrimitives)
    (hsafePrimitives : ∀ {n ci}, env'.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hleUnsafe : ves.venv .unsafe ≤ unsafeEnv) :
    ∃ ves' : VEnvs, ves'.WF env' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let next : DefinitionSafety → VEnv
    | .unsafe => unsafeEnv
    | .partial => ves.venv .partial
    | .safe => ves.venv .safe
  let ves' : VEnvs := ⟨next⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := hsafePrimitives
      mono := ?_ }
    · intro safety
      cases safety with
      | «unsafe» => exact htrUnsafe
      | «partial» => exact htrPartial
      | safe => exact htrSafe
    · intro safety
      cases safety with
      | «unsafe» => exact hunsafePrimitives
      | «partial» => exact wf.hasPrimitives
      | safe => exact wf.hasPrimitives
    · intro safety safety' hle
      cases safety <;> cases safety' <;>
        simp only [ves', next]
      · exact VEnv.LE.rfl
      · exact (wf.mono DefinitionSafety.unsafe_le).trans hleUnsafe
      · exact (wf.mono DefinitionSafety.unsafe_le).trans hleUnsafe
      · exact False.elim ((by decide : ¬ (DefinitionSafety.safe ≤
          DefinitionSafety.unsafe)) hle)
      · exact wf.mono DefinitionSafety.le_rfl
      · exact False.elim ((by decide : ¬ (DefinitionSafety.safe ≤
          DefinitionSafety.partial)) hle)
      · exact False.elim ((by decide : ¬ (DefinitionSafety.partial ≤
          DefinitionSafety.unsafe)) hle)
      · exact wf.mono DefinitionSafety.le_safe
      · exact wf.mono DefinitionSafety.le_rfl
  · intro safety
    cases safety with
    | «unsafe» => exact hleUnsafe
    | «partial» => exact VEnv.LE.rfl
    | safe => exact VEnv.LE.rfl

/-- Assemble the three safety-indexed results of one concrete inductive
extension.  All implementation-specific work is isolated in the pointwise
`AddInduct` witnesses; this theorem supplies the `TrEnv'` constructors,
cross-safety monotonicity, and old-to-new inclusions required by `VEnvs.WF`. -/
theorem VEnvs.WF.extendInduct
    {ves : VEnvs} {env env' : Environment} (wf : ves.WF env)
    (decl : VInductDecl) (next : DefinitionSafety → VEnv)
    (hadd : ∀ safety,
      AddInduct env.constants (ves.venv safety) decl
        env'.constants (next safety))
    (hquot : env'.quotInit = env.quotInit)
    (hprimitives : ∀ safety, (next safety).HasPrimitives)
    (hsafePrimitives : ∀ {n ci}, env'.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hmono : ∀ {safety safety'}, safety ≤ safety' →
      next safety' ≤ next safety) :
    ∃ ves' : VEnvs, ves'.WF env' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let ves' : VEnvs := ⟨next⟩
  refine ⟨ves', ?_, ?_⟩
  · exact {
      tr := by
        intro safety
        change TrEnv' safety env'.constants env'.quotInit (next safety)
        rw [hquot]
        exact TrEnv'.induct (hadd safety).declWF
          (hadd safety) (wf.tr (safety := safety))
      hasPrimitives := by
        intro safety
        exact hprimitives safety
      safePrimitives := hsafePrimitives
      mono := by
        intro _ _ hle
        exact hmono hle }
  · intro safety
    exact (hadd safety).le

theorem addConstCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (hprim : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (preserves : ∀ safety venv', safety ≤ ci.safety →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      (ves.venv safety).HasPrimitives → venv'.HasPrimitives)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have hnMap : env.constants.find? ci.name = none := by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hn
  have visible_tr (safety) (hvisible : safety ≤ ci.safety) :
      TrConstant safety (ves.venv safety) ci ci'.toVConstant :=
    (htr.1.sf_mono (visible_le safety hvisible)).mono (wf.mono (visible_le safety hvisible))
  have visible_wf (safety) (hvisible : safety ≤ ci.safety) :
      ci'.toVConstant.WF (ves.venv safety) :=
    hci.mono (wf.mono (visible_le safety hvisible))
  have hex (safety) (hvisible : safety ≤ ci.safety) :=
    (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
  let next (safety : DefinitionSafety) : VEnv :=
    if hvisible : safety ≤ ci.safety then Classical.choose (hex safety hvisible)
    else ves.venv safety
  have hadd (safety) (hvisible : safety ≤ ci.safety) :
      (ves.venv safety).addConst ci.name ci'.toVConstant = some (next safety) := by
    simpa [next, hvisible] using Classical.choose_spec (hex safety hvisible)
  let ves' : VEnvs := ⟨next⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := wf.safePrimitives_add ci hn hprim
      mono := ?_ }
    · intro safety
      change TrEnv' safety (env.constants.insert ci.name ci) env.quotInit (next safety)
      by_cases hvisible : safety ≤ ci.safety
      · exact step safety _ (visible_tr safety hvisible) (visible_wf safety hvisible)
          (hadd safety hvisible) (wf.tr (safety := safety))
      · simpa [next, hvisible] using
          TrEnv'.ignore (ci := ci) hnMap hvisible (wf.tr (safety := safety))
    · intro safety
      by_cases hvisible : safety ≤ ci.safety
      · exact preserves safety _ hvisible (hadd safety hvisible) wf.hasPrimitives
      · simpa [ves', next, hvisible] using wf.hasPrimitives (safety := safety)
    · intro safety safety' hle
      change next safety' ≤ next safety
      by_cases hvisible' : safety' ≤ ci.safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        rw [show next safety' = Classical.choose (hex safety' hvisible') by simp [next, hvisible'],
          show next safety = Classical.choose (hex safety hvisible) by simp [next, hvisible]]
        exact VEnv.addConst_mono (wf.mono hle)
          (Classical.choose_spec (hex safety' hvisible'))
          (Classical.choose_spec (hex safety hvisible))
      · rw [show next safety' = ves.venv safety' by simp [next, hvisible']]
        by_cases hvisible : safety ≤ ci.safety
        · rw [show next safety = Classical.choose (hex safety hvisible) by simp [next, hvisible]]
          exact (wf.mono hle).trans
            (VEnv.addConst_le (Classical.choose_spec (hex safety hvisible)))
        · rw [show next safety = ves.venv safety by simp [next, hvisible]]
          exact wf.mono hle
  · intro safety
    change ves.venv safety ≤ next safety
    by_cases hvisible : safety ≤ ci.safety
    · simpa [next, hvisible] using VEnv.addConst_le (hadd safety hvisible)
    · simp [next, hvisible, VEnv.LE.rfl]

theorem addConst.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (hnonprim : Environment.primitives.contains ci.name = false)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  exact addConstCore.WF wf ci ci' checkSafety visible_le htr hci hn
    (fun hp => by simp_all)
    (fun _ _ _ hadd hp => hp.addConst hnonprim hadd) step

theorem addDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ (ConstantInfo.defnInfo v).safety → safety ≤ checkSafety)
    (htr : TrDefVal checkSafety (ves.venv checkSafety) (.defnInfo v) ci')
    (hci : ci'.WF (ves.venv checkSafety))
    (hn : env.find? v.name = none)
    (hprim : Environment.primitives.contains v.name →
      (ConstantInfo.defnInfo v).safety = .safe ∧ v.levelParams = [])
    (preserves : ∀ safety base,
      safety ≤ (ConstantInfo.defnInfo v).safety →
      (ves.venv safety).addConst v.name ci'.toVConstant = some base →
      (base.addDefEq ci'.toDefEq).HasPrimitives) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have hnMap : env.constants.find? v.name = none := by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hn
  have visible_tr (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      TrDefVal safety (ves.venv safety) (.defnInfo v) ci' := by
    have htr' : TrDefVal safety (ves.venv checkSafety) (.defnInfo v) ci' :=
      ⟨⟨htr.1.1.sf_mono (visible_le safety hvisible), htr.1.2⟩, htr.2⟩
    exact htr'.mono (wf.mono (visible_le safety hvisible))
  have visible_wf (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      ci'.WF (ves.venv safety) := hci.mono (wf.mono (visible_le safety hvisible))
  have hex (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :=
    (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
  let base (safety : DefinitionSafety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :=
    Classical.choose (hex safety hvisible)
  let next (safety : DefinitionSafety) : VEnv :=
    if hvisible : safety ≤ (ConstantInfo.defnInfo v).safety then
      (base safety hvisible).addDefEq ci'.toDefEq
    else ves.venv safety
  have hadd (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      (ves.venv safety).addConst v.name ci'.toVConstant = some (base safety hvisible) :=
    Classical.choose_spec (hex safety hvisible)
  let ves' : VEnvs := ⟨next⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := wf.safePrimitives_add (.defnInfo v) hn hprim
      mono := ?_ }
    · intro safety
      change TrEnv' safety (env.constants.insert v.name (.defnInfo v)) env.quotInit (next safety)
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · simpa [next, hvisible] using TrEnv'.defn (visible_tr safety hvisible)
          (by rwa [← (wf.tr (safety := safety)).map_wf.find?'_eq_find?])
          (visible_wf safety hvisible) (hadd safety hvisible) (wf.tr (safety := safety))
      · simpa [next, hvisible, ConstantInfo.name, ConstantInfo.toConstantVal] using
          TrEnv'.ignore (ci := .defnInfo v) hnMap hvisible (wf.tr (safety := safety))
    · intro safety
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · simpa [ves', next, hvisible] using preserves safety (base safety hvisible)
          hvisible (hadd safety hvisible)
      · simpa [ves', next, hvisible] using wf.hasPrimitives (safety := safety)
    · intro safety safety' hle
      change next safety' ≤ next safety
      by_cases hvisible' : safety' ≤ (ConstantInfo.defnInfo v).safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        rw [show next safety' = (base safety' hvisible').addDefEq ci'.toDefEq by
              simp [next, hvisible'],
          show next safety = (base safety hvisible).addDefEq ci'.toDefEq by
              simp [next, hvisible]]
        exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hle)
          (hadd safety' hvisible') (hadd safety hvisible)
      · rw [show next safety' = ves.venv safety' by simp [next, hvisible']]
        by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
        · rw [show next safety = (base safety hvisible).addDefEq ci'.toDefEq by
              simp [next, hvisible]]
          exact (wf.mono hle).trans <| (VEnv.addConst_le (hadd safety hvisible)).trans
            VEnv.addDefEq_le
        · rw [show next safety = ves.venv safety by simp [next, hvisible]]
          exact wf.mono hle
  · intro safety
    change ves.venv safety ≤ next safety
    by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
    · rw [show next safety = (base safety hvisible).addDefEq ci'.toDefEq by
          simp [next, hvisible]]
      exact (VEnv.addConst_le (hadd safety hvisible)).trans VEnv.addDefEq_le
    · simp [next, hvisible, VEnv.LE.rfl]
