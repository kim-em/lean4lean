import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Quot

/-!
# Recursor rules as a checking invariant

The executable checker reduces a recursor application by looking up the `RecursorRule` for the
constructor at the head of the major premise. The abstract environment stores each such rule as a
closed lambda-wrapped equation. This file states, for a checking environment, that every visible
recursor's rules are stored equations of the shape `VIotaRuleShape`, that the recursor's type and
each constructor's type have the shapes `VRecursorShape` and `VConstructorShape`, that the major
inductive type constant is rigid, and (for K-like recursors) that the inductive type is a
proposition whose parameters type the unique constructor. The quotient reduction rules are covered
by the same shapes for `Quot.lift`, and by proof irrelevance for `Quot.ind`.
-/

namespace Lean4Lean
open Lean

/-- The stored equation `df` is the iota rule of `rec` for `rule`: it has the rule shape, its
right-hand side translates the executable rule's right-hand side, and the rule's constructor has
the constructor shape at `cnparams` parameters. -/
structure RecursorRuleAlignment (venv : VEnv) (rec : RecursorVal) (rule : RecursorRule)
    (indLevels : List VLevel) (cnparams : Nat) (df : VDefEq) : Prop where
  shape : Nonempty (VIotaRuleShape venv rec.name rec.levelParams.length rec.numParams cnparams
    rec.numMotives rec.numMinors rec.numIndices rule.ctor indLevels rule.nfields df)
  rhs : TrExprS venv rec.levelParams [] rule.rhs df.rhs
  ctor : ∃ ctorUvars, indLevels.length = ctorUvars ∧
    Nonempty (VConstructorShape venv rule.ctor ctorUvars cnparams rule.nfields rec.numIndices
      rec.getMajorInduct)

/-- The recursor `rec` has the recursor shape with `cnparams` constructor parameters, its major
inductive is rigid, and every rule is a stored equation. -/
def RecursorAlignment (venv : VEnv) (rec : RecursorVal) (cnparams : Nat) : Prop :=
  ∃ indLevels, cnparams ≤ rec.numParams ∧
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
      rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels) ∧
    venv.Rigid rec.getMajorInduct ∧
    ∀ rule ∈ rec.rules, ∃ df, RecursorRuleAlignment venv rec rule indLevels cnparams df

/-- A K-like recursor eliminates from a proposition with a single constructor whose only
arguments are the parameters; the constructor's parameter binders are definitionally the
inductive type's parameter binders, under the binders before them. -/
def KLikeAlignment (venv : VEnv) (rec : RecursorVal) (ctorName : Name) : Prop :=
  ∃ indUvars indDoms ctorDoms ctorBody,
    venv.constants rec.getMajorInduct = some ⟨indUvars, VExpr.wrapForalls indDoms (.sort .zero)⟩ ∧
    indDoms.length = rec.numParams + rec.numIndices ∧
    venv.constants ctorName = some ⟨indUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ ∧
    ctorDoms.length = rec.numParams ∧
    ∀ k (hk : k < indDoms.length) (hk' : k < ctorDoms.length),
      venv.IsDefEqU indUvars ((indDoms.take k).reverse) indDoms[k] ctorDoms[k]

/-- Every visible recursor of the constant map is aligned with the abstract environment. -/
def RecursorRulesCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) → safety ≤ (ConstantInfo.recInfo rec).safety →
    RecursorAlignment venv rec rec.numParams ∧
    (rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
      info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName)

/-- The quotient constants and the `Quot.lift` equation are present, and `Quot` is rigid. -/
structure QuotCoherent (venv : VEnv) : Prop where
  quot : venv.constants ``Quot = some quotConst
  quotMk : venv.constants ``Quot.mk = some quotMkConst
  lift : venv.constants ``Quot.lift = some quotLiftConst
  ind : venv.constants ``Quot.ind = some quotIndConst
  defeq : venv.defeqs quotDefEq
  rigid : venv.Rigid ``Quot

variable {venv : VEnv}

/-- `Quot.lift` has the recursor shape with five parameters, of which the first two are the
parameters of `Quot.mk`. -/
def QuotCoherent.liftRecursorShape (H : QuotCoherent venv) :
    VRecursorShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot [.param 0] where
  type := quotLiftConst.type
  const := H.lift
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]
  result := .bvar 3
  type_eq := rfl
  doms_length := rfl
  major_eq := rfl

/-- `Quot.mk` has the constructor shape with two parameters and one field. -/
def QuotCoherent.mkConstructorShape (H : QuotCoherent venv) :
    VConstructorShape venv ``Quot.mk 1 2 1 0 ``Quot where
  type := quotMkConst.type
  const := H.quotMk
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
  indices := []
  type_eq := rfl
  doms_length := rfl
  indices_length := rfl

/-- The `Quot.lift` equation has the iota rule shape. -/
def QuotCoherent.liftRuleShape (H : QuotCoherent venv) :
    VIotaRuleShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot.mk [.param 0] 1 quotDefEq where
  defeq := H.defeq
  uvars := rfl
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .bvar 4]
  lhsBody := quotDefEq.lhs.stripLams
  rhsBody := .app (.bvar 2) (.bvar 0)
  typeBody := .bvar 3
  lhs_eq := rfl
  rhs_eq := rfl
  type_eq := rfl
  doms_length := rfl
  indexArgs := []
  indexArgs_length := rfl
  lhs_pattern := rfl

/-- A lift over more binders than the instantiation depth is cancelled one step. -/
@[simp] theorem _root_.Lean4Lean.VExpr.inst_liftN_lt (e a : VExpr) {k m : Nat} (h : k < m) :
    (VExpr.liftN m e).inst a k = VExpr.liftN (m - 1) e := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 + k := ⟨m - 1 - k, by omega⟩
  rw [← VExpr.liftN'_liftN_lo e (n + 1) k, VExpr.inst_liftN', VExpr.liftN'_liftN_lo]
  congr 1; omega

/-- `Quot.ind` reduces by proof irrelevance: applied to a term convertible to `Quot.mk α r a`, it
is definitionally equal to its minor premise applied to `a`. -/
theorem QuotCoherent.ind_defeq (henv : VEnv.WF venv) (hΓ : OnCtx Γ (venv.IsType U))
    (hq : QuotCoherent venv) {ls' lsm' : List VLevel}
    (hls'w : ∀ l ∈ ls', l.WF U) (hls'len : ls'.length = 1)
    (hlsm'w : ∀ l ∈ lsm', l.WF U) (hlsm'len : lsm'.length = 1)
    {α' r' β' p' q' a1' a2' a3' : VExpr}
    (hwf : VExpr.WF venv U Γ (VExpr.mkApps (.const ``Quot.ind ls') [α', r', β', p', q']))
    (hmkwf : VExpr.WF venv U Γ (VExpr.mkApps (.const ``Quot.mk lsm') [a1', a2', a3']))
    (hmk : venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot.mk lsm') [a1', a2', a3']) q') :
    venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot.ind ls') [α', r', β', p', q'])
      (.app p' a3') := by
  obtain ⟨u', rfl⟩ : ∃ u', ls' = [u'] := match ls', hls'len with | [u'], _ => ⟨u', rfl⟩
  obtain ⟨um', rfl⟩ : ∃ um', lsm' = [um'] := match lsm', hlsm'len with | [um'], _ => ⟨um', rfl⟩
  have hu' : u'.WF U := hls'w _ (List.mem_singleton.2 rfl)
  have hum' : um'.WF U := hlsm'w _ (List.mem_singleton.2 rfl)
  -- the eliminator spine
  have hc := VEnv.HasType.const (Γ := Γ) hq.ind hls'w rfl
  have ⟨hargsT, hres⟩ := VEnv.HasType.mkApps_wrapForalls henv hΓ (doms :=
      [.sort u', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
       .forallE (.app (.app (.const ``Quot [u']) (.bvar 1)) (.bvar 0)) (.sort .zero),
       .forallE (.bvar 2) (.app (.bvar 1)
         (.app (.app (.app (.const ``Quot.mk [u']) (.bvar 3)) (.bvar 2)) (.bvar 0))),
       .app (.app (.const ``Quot [u']) (.bvar 3)) (.bvar 2)])
    (body := .app (.bvar 2) (.bvar 0)) hc hwf rfl
  have hβ : venv.HasType U Γ β'
      (.forallE (.app (.app (.const ``Quot [u']) α') r') (.sort .zero)) := by
    have := hargsT 2 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hp : venv.HasType U Γ p'
      (.forallE α' (.app (VExpr.liftN 1 β')
        (.app (.app (.app (.const ``Quot.mk [u']) (VExpr.liftN 1 α')) (VExpr.liftN 1 r'))
          (.bvar 0)))) := by
    have := hargsT 3 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hq' : venv.HasType U Γ q' (.app (.app (.const ``Quot [u']) α') r') := by
    have := hargsT 4 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hX1 : venv.HasType U Γ (VExpr.mkApps (.const ``Quot.ind [u']) [α', r', β', p', q'])
      (.app β' q') := by
    simpa [VExpr.inst, VExpr.instVar] using hres
  -- the constructor spine
  have hcm := VEnv.HasType.const (Γ := Γ) hq.quotMk hlsm'w rfl
  have ⟨hmargsT, hmres⟩ := VEnv.HasType.mkApps_wrapForalls henv hΓ (doms :=
      [.sort um', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1])
    (body := .app (.app (.const ``Quot [um']) (.bvar 2)) (.bvar 1)) hcm hmkwf rfl
  have ha1 : venv.HasType U Γ a1' (.sort um') := by
    have := hmargsT 0 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have ha2 : venv.HasType U Γ a2' (.forallE a1' (.forallE (VExpr.liftN 1 a1') (.sort .zero))) := by
    have := hmargsT 1 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have ha3 : venv.HasType U Γ a3' a1' := by
    have := hmargsT 2 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hmkT : venv.HasType U Γ (VExpr.mkApps (.const ``Quot.mk [um']) [a1', a2', a3'])
      (.app (.app (.const ``Quot [um']) a1') a2') := by
    simpa [VExpr.inst, VExpr.instVar] using hmres
  -- injectivity of `Quot`
  have hQQ : venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot [u']) [α', r'])
      (VExpr.mkApps (.const ``Quot [um']) [a1', a2']) :=
    ((hmk.symm.of_l henv hΓ hq').hasType.2).uniqU henv hΓ hmkT
  have ⟨_, hsort⟩ := hq'.isType henv.ordered hΓ
  have ⟨hlv, hargsE⟩ := VEnv.IsDefEqU.rigidApp_inv henv hΓ hq.rigid hQQ hsort
  have hαa : venv.IsDefEqU U Γ α' a1' := List.forall₂_getElem hargsE 0 (by simp) (by simp)
  have hra : venv.IsDefEqU U Γ r' a2' := List.forall₂_getElem hargsE 1 (by simp) (by simp)
  have huu : u' ≈ um' := List.forall₂_getElem hlv 0 (by simp) (by simp)
  -- `Quot.mk um' a1' a2' a3' ≡ Quot.mk u' α' r' a3'`
  have hcDF : venv.IsDefEq U Γ (.const ``Quot.mk [um']) (.const ``Quot.mk [u'])
      (VExpr.wrapForalls [.sort um', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
        (.app (.app (.const ``Quot [um']) (.bvar 2)) (.bvar 1))) :=
    VEnv.IsDefEq.constDF hq.quotMk hlsm'w hls'w rfl
      (.cons (VLevel.equiv_def'.2 (VLevel.equiv_def'.1 huu).symm) .nil)
  have hcongr := VEnv.IsDefEq.mkApps_congr henv hΓ (args := [a1', a2', a3']) (args' := [α', r', a3'])
    hcDF rfl rfl (by
      intro j hj hj' hj''
      match j, hj with
      | 0, _ => exact hαa.symm.of_l henv hΓ ha1
      | 1, _ =>
        refine hra.symm.of_l henv hΓ ?_
        simpa [VExpr.inst, VExpr.instVar] using ha2
      | 2, _ =>
        show venv.HasType U Γ a3' _
        simpa [VExpr.inst, VExpr.instVar] using ha3)
  simp [VExpr.inst, VExpr.instVar] at hcongr
  have hmk1 : venv.IsDefEq U Γ (VExpr.mkApps (.const ``Quot.mk [um']) [a1', a2', a3'])
      (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])
      (VExpr.mkApps (.const ``Quot [u']) [α', r']) :=
    VEnv.IsDefEqU.defeqDF henv hΓ hQQ.symm hcongr
  have hqmk : venv.IsDefEq U Γ q' (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])
      (VExpr.mkApps (.const ``Quot [u']) [α', r']) :=
    (hmk.symm.of_l henv hΓ hq').trans hmk1
  have ha3α : venv.HasType U Γ a3' α' := ha3.defeqU_r henv hΓ hαa.symm
  have hX2 := hp.app ha3α
  simp [VExpr.inst, VExpr.instVar] at hX2
  have hβsort : venv.HasType U Γ (.app β' q') (.sort .zero) := by
    simpa [VExpr.inst] using hβ.app hq'
  have htyeq : venv.IsDefEq U Γ (.app β' q')
      (.app β' (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])) (.sort .zero) := by
    simpa [VExpr.inst] using hβ.appDF hqmk
  have hX2' : venv.HasType U Γ (.app p' a3') (.app β' q') :=
    hX2.defeqU_r henv hΓ ⟨_, htyeq.symm⟩
  exact ⟨_, VEnv.IsDefEq.proofIrrel hβsort hX1 hX2'⟩

/-! ## Monotonicity

The shape invariants only look up constants and stored equations, so they are preserved by
environment extension. Rigidity is not: it is preserved exactly when the new stored equations are
headed elsewhere, which is what `RigidPreserving` records. -/

/-- Every constant rigid in `venv` stays rigid in `venv'`. -/
def VEnv.RigidPreserving (venv venv' : VEnv) : Prop := ∀ c, venv.Rigid c → venv'.Rigid c

theorem VEnv.RigidPreserving.rfl : VEnv.RigidPreserving venv venv := fun _ h => h

theorem VEnv.RigidPreserving.trans (h1 : VEnv.RigidPreserving venv₁ venv₂)
    (h2 : VEnv.RigidPreserving venv₂ venv₃) : VEnv.RigidPreserving venv₁ venv₃ :=
  fun c h => h2 c (h1 c h)

theorem VEnv.RigidPreserving.addConst (h : venv.addConst name ci = some venv') :
    VEnv.RigidPreserving venv venv' := by
  intro c hc df hdf
  unfold VEnv.addConst at h
  split at h <;> cases h
  exact hc df hdf

/-- Adding an equation headed (under its lambdas) by a constant that is not `c` keeps `c` rigid. -/
theorem VEnv.Rigid.addDefEq (hc : venv.Rigid c) (hhead : ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c ls) :
    (venv.addDefEq df).Rigid c := by
  intro df' hdf' ls
  rcases hdf' with rfl | hdf'
  · exact hhead ls
  · exact hc df' hdf' ls

/-- Adding an equation headed by a constant not yet in the environment keeps every existing
constant rigid. -/
theorem VEnv.RigidPreserving.addDefEq_fresh {head : Name}
    (hhead : ∀ ls, df.lhs.stripLams.getAppFnArgs.1 = .const head ls)
    (hfresh : venv.constants head = none) :
    ∀ c, venv.contains c → venv.Rigid c → (venv.addDefEq df).Rigid c := by
  intro c ⟨ci, hci⟩ hc
  refine hc.addDefEq fun ls h => ?_
  rw [hhead ls] at h
  cases h
  rw [hfresh] at hci
  cases hci

theorem VEnv.RigidPreserving.addProjections (entries : List VProjectionEntry) :
    VEnv.RigidPreserving venv (venv.addProjections entries) := by
  intro c hc df hdf
  rw [VEnv.addProjections_defeqs] at hdf
  exact hc df hdf

def VRecursorShape.mono (h : venv ≤ venv')
    (H : VRecursorShape venv recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels) :
    VRecursorShape venv' recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels :=
  { H with const := h.constants H.const }

def VConstructorShape.mono (h : venv ≤ venv')
    (H : VConstructorShape venv ctorName ctorUvars nparams nfields nindices indName) :
    VConstructorShape venv' ctorName ctorUvars nparams nfields nindices indName :=
  { H with const := h.constants H.const }

def VIotaRuleShape.mono (h : venv ≤ venv')
    (H : VIotaRuleShape venv recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df) :
    VIotaRuleShape venv' recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df :=
  { H with defeq := h.defeqs H.defeq }

theorem RecursorRuleAlignment.mono {rec : RecursorVal} (h : venv ≤ venv')
    (H : RecursorRuleAlignment venv rec rule indLevels cnparams df) :
    RecursorRuleAlignment venv' rec rule indLevels cnparams df where
  shape := H.shape.elim fun s => ⟨s.mono h⟩
  rhs := H.rhs.mono h
  ctor := H.ctor.elim fun u ⟨hu, hs⟩ => ⟨u, hu, hs.elim fun s => ⟨s.mono h⟩⟩

theorem RecursorAlignment.mono (h : venv ≤ venv') (hr : VEnv.RigidPreserving venv venv')
    (H : RecursorAlignment venv rec cnparams) : RecursorAlignment venv' rec cnparams :=
  let ⟨indLevels, hle, ⟨s⟩, hrigid, hrules⟩ := H
  ⟨indLevels, hle, ⟨s.mono h⟩, hr _ hrigid, fun rule hrule =>
    let ⟨df, hdf⟩ := hrules rule hrule; ⟨df, hdf.mono h⟩⟩

theorem KLikeAlignment.mono (h : venv ≤ venv')
    (H : KLikeAlignment venv rec ctorName) : KLikeAlignment venv' rec ctorName := by
  obtain ⟨indUvars, indDoms, ctorDoms, ctorBody, hI, hIlen, hC, hClen, hparams⟩ := H
  refine ⟨indUvars, indDoms, ctorDoms, ctorBody, h.constants hI, hIlen, h.constants hC, hClen, ?_⟩
  intro k hk hk'
  exact (hparams k hk hk').mono h

theorem QuotCoherent.mono (h : venv ≤ venv') (hr : VEnv.RigidPreserving venv venv')
    (H : QuotCoherent venv) : QuotCoherent venv' where
  quot := h.constants H.quot
  quotMk := h.constants H.quotMk
  lift := h.constants H.lift
  ind := h.constants H.ind
  defeq := h.defeqs H.defeq
  rigid := hr _ H.rigid

/-! ## The quotient step of the environment trace -/

theorem VEnv.addConst_defeqs {env env' : VEnv} (h : env.addConst name ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  rfl

/-- Initializing quotients yields the quotient invariant, provided no equation already present is
headed by `Quot` (a fresh constant cannot head an equation of a well-formed environment). -/
theorem AddQuot.quotCoherent (H : AddQuot m₁ m₂ venv₁ venv₂)
    (hrigid : venv₁.Rigid ``Quot) : QuotCoherent venv₂ := by
  obtain ⟨_, _, e1, -, -, h1, _, _, e2, -, -, h2, _, _, e3, -, -, h3, _, _, e4, -, -, h4, -, rfl⟩ := H
  have le1 := VEnv.addConst_le h1
  have le2 := VEnv.addConst_le h2
  have le3 := VEnv.addConst_le h3
  have le4 := VEnv.addConst_le h4
  have le5 : e4 ≤ e4.addDefEq quotDefEq := VEnv.addDefEq_le
  refine ⟨?_, ?_, ?_, ?_, Or.inl rfl, ?_⟩
  · exact le5.constants (le4.constants (le3.constants (le2.constants (VEnv.addConst_self h1))))
  · exact le5.constants (le4.constants (le3.constants (VEnv.addConst_self h2)))
  · exact le5.constants (le4.constants (VEnv.addConst_self h3))
  · exact le5.constants (VEnv.addConst_self h4)
  · refine VEnv.Rigid.addDefEq ?_ fun ls h => by cases h
    intro df hdf
    rw [VEnv.addConst_defeqs h4, VEnv.addConst_defeqs h3, VEnv.addConst_defeqs h2,
      VEnv.addConst_defeqs h1] at hdf
    exact hrigid df hdf

/-! ## Heads of stored equations

Rigidity of an inductive type constant follows from a global property of the environment: every
stored equation is headed, under its lambdas, by a constant of the production map that is not an
inductive type (a definition, a recursor, or `Quot.lift`). This is the property to carry along the
environment trace. -/

/-- Every stored equation is headed by a constant of `C` that is neither an inductive type nor a
quotient constant other than `Quot.lift`. -/
def EquationHeadsCoherent (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ df, venv.defeqs df → ∃ head ls ci, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
    C.find? head = some ci ∧ (∀ info, ci ≠ .inductInfo info) ∧
    (∀ q, ci = .quotInfo q → q.kind = .lift)

theorem EquationHeadsCoherent.rigid (H : EquationHeadsCoherent C venv)
    (h : C.find? n = some (.inductInfo info)) : venv.Rigid n := by
  intro df hdf ls heq
  obtain ⟨head, ls', ci, hhead, hci, hne, -⟩ := H df hdf
  rw [heq] at hhead
  cases hhead
  rw [h] at hci
  exact hne info (Option.some.inj hci).symm

theorem EquationHeadsCoherent.rigid_quot (H : EquationHeadsCoherent C venv)
    (h : C.find? ``Quot = some (.quotInfo q)) (hk : q.kind = .type) : venv.Rigid ``Quot := by
  intro df hdf ls heq
  obtain ⟨head, ls', ci, hhead, hci, -, hq⟩ := H df hdf
  rw [heq] at hhead
  cases hhead
  rw [h] at hci
  have := hq q (Option.some.inj hci).symm
  rw [hk] at this
  cases this

theorem EquationHeadsCoherent.mapExt (H : EquationHeadsCoherent C venv)
    (h : ∀ name, C.find? name = C'.find? name) : EquationHeadsCoherent C' venv := by
  intro df hdf
  obtain ⟨head, ls, ci, hhead, hci, hne, hq⟩ := H df hdf
  exact ⟨head, ls, ci, hhead, (h head).symm.trans hci, hne, hq⟩

theorem EquationHeadsCoherent.insert (H : EquationHeadsCoherent C venv) (hwf : C.WF)
    (hfresh : C.find? n = none) : EquationHeadsCoherent (C.insert n ci) venv := by
  intro df hdf
  obtain ⟨head, ls, ci', hhead, hci, hne, hq⟩ := H df hdf
  refine ⟨head, ls, ci', hhead, ?_, hne, hq⟩
  rw [hwf.find?_insert]
  split
  · rename_i heq; rw [beq_iff_eq] at heq; subst heq; rw [hfresh] at hci; cases hci
  · exact hci

theorem EquationHeadsCoherent.addConst (H : EquationHeadsCoherent C venv)
    (h : venv.addConst n ci = some venv') : EquationHeadsCoherent C venv' := by
  intro df hdf
  rw [VEnv.addConst_defeqs h] at hdf
  exact H df hdf

theorem EquationHeadsCoherent.addProjections (H : EquationHeadsCoherent C venv)
    (entries : List VProjectionEntry) : EquationHeadsCoherent C (venv.addProjections entries) := by
  intro df hdf
  rw [VEnv.addProjections_defeqs] at hdf
  exact H df hdf

/-- Adding an equation headed by a non-inductive constant of `C`. -/
theorem EquationHeadsCoherent.addDefEq (H : EquationHeadsCoherent C venv)
    (hhead : ∃ head ls ci, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
      C.find? head = some ci ∧ (∀ info, ci ≠ .inductInfo info) ∧
      (∀ q, ci = .quotInfo q → q.kind = .lift)) :
    EquationHeadsCoherent C (venv.addDefEq df) := by
  intro df' hdf'
  rcases hdf' with rfl | hdf'
  · exact hhead
  · exact H df' hdf'

end Lean4Lean
