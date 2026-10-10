import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Quot
import Lean4Lean.Inductive.Add

/-!
# What the checker reads of its environment

The verification of the type checker (`Verify/TypeChecker/**`) runs against an abstract
environment `venv` and reads a fixed list of facts relating it to the executable environment
`env`: the constant translation (`CheckingEnv`), the constructor and projection metadata of the
installed inductive blocks, the shapes of the visible recursors and the ι rules registered for
them, and the quotient constants. `CheckerEnv` collects exactly these facts, so that the
checker proofs do not depend on how the environment invariant establishes them.

`CheckingEnv` is the fragment of `TrEnv` that also describes the intermediate environments of an
inductive declaration (headers, constructors) in which the inductive checker runs the type
checker. The ι rules are read in the form of PR #43's `TrEnv.pats_iota'`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Kernel environments do not contain dangling or unlisted constructor
metadata: every constructor's recorded inductive owner is itself present,
lists the constructor, and has the constructor's `isUnsafe`.  This is a
persistent kernel-environment invariant, not a nested-lowering premise.  It
also holds in the environments an inductive declaration builds while it is
checked, because a constructor is only added after the header that lists it. -/
def ConstructorOwnersPresent (env : Environment) : Prop :=
  ∀ name info, env.find? name = some (.ctorInfo info) →
    ∃ owner, env.find? info.induct = some (.inductInfo owner) ∧
      name ∈ owner.ctors ∧ info.isUnsafe = owner.isUnsafe

/-- Every constructor name that a present inductive header lists is, if present, a
constructor whose recorded inductive is that header, with the header's `isUnsafe`.  Presence
is a premise because while an inductive declaration is checked its headers are installed
before the constructors they list; on a complete environment this follows from
`InductiveConstructorsCoherent`. -/
def ListedConstructorsCoherent (env : Environment) : Prop :=
  ∀ familyName familyInfo, env.find? familyName = some (.inductInfo familyInfo) →
    ∀ name ∈ familyInfo.ctors, ∀ ci, env.find? name = some ci →
      ∃ info, ci = .ctorInfo info ∧ info.induct = familyName ∧
        info.isUnsafe = familyInfo.isUnsafe

end VerifyInductive

/-- Exact agreement between a concrete singleton inductive family and the
primitive-projection entry available in its abstract checking environment.
This is the persistent invariant consumed by projection inference: it records
precisely the executable metadata read by `inferProj` and `reduceProjCore`
(parameter and index counts, universe arity, the constructor's identity and
field count) against the registered abstract entry, and the abstract
constants named by that entry. -/
structure ProjectionRegistryAlignmentAt
    (C : ConstMap) (env : VEnv) (familyName : Name)
    (familyInfo : InductiveVal) (constructorName : Name) where
  info : VProjectionInfo
  projection : env.projections familyName info
  ctorName : info.ctorName = constructorName
  uvars : familyInfo.levelParams.length = info.uvars
  nparams : familyInfo.numParams = info.nparams
  nindices : familyInfo.numIndices = info.nindices
  constructorInfo : ConstructorVal
  constructor_lookup : C.find? constructorName = some (.ctorInfo constructorInfo)
  constructor_induct : constructorInfo.induct = familyName
  constructor_levelParams : constructorInfo.levelParams = familyInfo.levelParams
  constructor_numParams : constructorInfo.numParams = familyInfo.numParams
  constructor_isUnsafe : constructorInfo.isUnsafe = familyInfo.isUnsafe
  constructor_numFields : constructorInfo.numFields = info.numFields
  /-- The field count is the syntactic arity of the stored constructor type beyond the
  parameters (`AddInductive.constructorInfo`); the projection walk reads it to know that the
  stored type is a syntactic `forallE` spine up to the selected field. -/
  constructor_arity : constructorInfo.numFields =
    AddInductive.constructorArity constructorInfo.type - constructorInfo.numParams
  familyType : VExpr
  family_lookup : env.constants familyName = some ⟨info.uvars, familyType⟩
  constructor_abstract :
    env.constants constructorName = some ⟨info.uvars, info.ctorType⟩

/-- Every executable singleton-family lookup that is visible at this safety
level, whose listed constructor is present and names the family as its
owner, has matching primitive-projection metadata in the abstract model. -/
def ProjectionRegistryCoherent
    (safety : DefinitionSafety) (C : ConstMap) (env : VEnv) : Prop :=
  ∀ familyName familyInfo constructorName constructorInfo,
    C.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (ConstantInfo.inductInfo familyInfo).safety →
    familyInfo.ctors = [constructorName] →
    C.find? constructorName = some (.ctorInfo constructorInfo) →
    constructorInfo.induct = familyName →
    Nonempty (ProjectionRegistryAlignmentAt C env familyName familyInfo
      constructorName)

/-- A K-like recursor eliminates from a proposition with a single constructor whose only
arguments are the parameters. Stored headers and constructor types may require reduction
to expose these telescopes (for example, a header ending in `id Prop`). The constructor's
parameter binders agree with the inductive's binders by typed equality. -/
def KLikeAlignment (venv : VEnv) (rec : RecursorVal) (ctorName : Name) : Prop :=
  ∃ indUvars indType ctorType indDoms ctorDoms ctorBody,
    venv.constants rec.getMajorInduct = some ⟨indUvars, indType⟩ ∧
    venv.IsDefEqU indUvars [] indType (VExpr.wrapForalls indDoms (.sort .zero)) ∧
    indDoms.length = rec.numParams + rec.numIndices ∧
    venv.constants ctorName = some ⟨indUvars, ctorType⟩ ∧
    venv.IsDefEqU indUvars [] ctorType (VExpr.wrapForalls ctorDoms ctorBody) ∧
    ctorDoms.length = rec.numParams ∧
    ∀ k (hk : k < indDoms.length) (hk' : k < ctorDoms.length),
      venv.IsDefEqU indUvars ((indDoms.take k).reverse) indDoms[k] ctorDoms[k]

/-- The quotient constants and the `Quot.lift` equation are present, and `Quot` is rigid. -/
structure QuotCoherent (venv : VEnv) : Prop where
  quot : venv.constants ``Quot = some quotConst
  quotMk : venv.constants ``Quot.mk = some quotMkConst
  lift : venv.constants ``Quot.lift = some quotLiftConst
  ind : venv.constants ``Quot.ind = some quotIndConst
  defeq : venv.defeqs quotDefEq
  rigid : venv.Rigid ``Quot

/-- The quotient facts carried through a checking environment: the abstract quotient constants and
equation, together with the kernel entry of `Quot` (which is what keeps `Quot` rigid along
the translation). -/
structure QuotEnvCoherent (C : ConstMap) (venv : VEnv) : Prop where
  coherent : QuotCoherent venv
  find : ∃ q : QuotVal, C.find? ``Quot = some (.quotInfo q) ∧ q.kind = .type

/-- The shapes of a visible recursor: its type is a recursor telescope over its major family, the
major family is rigid, and the constructor of each rule has the constructor telescope at the
recursor's constructor parameter count, which is the constructor's own parameter count. -/
def RecursorShapes (C : ConstMap) (venv : VEnv) (rec : RecursorVal) : Prop :=
  ∃ cnparams indLevels ctorParams,
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
      rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels ctorParams) ∧
    venv.Rigid rec.getMajorInduct ∧
    ∀ rule ∈ rec.rules, ∃ ctorUvars, indLevels.length = ctorUvars ∧
      Nonempty (VConstructorShape venv rule.ctor ctorUvars cnparams rule.nfields rec.numIndices
        rec.getMajorInduct) ∧
      ∀ cval, C.find? rule.ctor = some (.ctorInfo cval) → cval.numParams = cnparams

/-- Every visible recursor has its shapes, and a K-like one eliminates a single-constructor
family whose constructor is aligned (`KLikeAlignment`). -/
def RecursorsCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) →
    safety ≤ (ConstantInfo.recInfo rec).safety →
    RecursorShapes C venv rec ∧
    (rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
      info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName)

/-- The ι rule of every rule of a visible recursor is registered: PR #43's `TrEnv.pats_iota'`. -/
def IotaRulesRegistered (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  ∀ {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule},
    env.find? recName = some (.recInfo rval) →
    rval.rules.find? (·.ctor == cName) = some rule →
    safety ≤ (Lean.ConstantInfo.recInfo rval).safety →
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      env.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true)

/-- The fragment of `TrEnv` needed by the executable type checker. Unlike
`TrEnv`, this invariant does not assert that the current kernel environment
was assembled from complete declarations, so it can also describe the
header and constructor environments used while checking an inductive block. -/
structure CheckingEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop where
  aligned : Aligned safety env.constants venv
  wf : venv.WF
  of_value : env.find? name = some ci → safety ≤ ci.safety → ci.deltaValue? = some v →
    TrExpr venv ci.levelParams [] v
      (.const ci.name (VLevel.params ci.levelParams.length))

theorem TrEnv.toChecking (H : TrEnv safety env venv) : CheckingEnv safety env venv where
  aligned := H.aligned
  wf := H.wf
  of_value := H.of_value

theorem CheckingEnv.map_wf (H : CheckingEnv safety env venv) : env.constants.WF :=
  H.aligned.map_wf

theorem CheckingEnv.find?_iff (H : CheckingEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem CheckingEnv.find? (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem CheckingEnv.find?_uniq (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

/-- Everything the checker verification reads of its environment. -/
structure CheckerEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop
    extends CheckingEnv safety env venv where
  /-- Every constructor's owner is present and lists it. -/
  constructorOwners : VerifyInductive.ConstructorOwnersPresent env
  /-- Every listed constructor that is present is a constructor of its header. -/
  listedConstructors : VerifyInductive.ListedConstructorsCoherent env
  /-- Every visible structure is registered in the projection table. -/
  projectionRegistry : ProjectionRegistryCoherent safety env.constants venv
  /-- Every registered structure is a visible header with its constructor present. -/
  projectionHeader : ∀ {S info}, venv.projections S info →
    ∃ v : InductiveVal, env.find? S = some (.inductInfo v) ∧ v.ctors = [info.ctorName] ∧
      safety ≤ (ConstantInfo.inductInfo v).safety ∧
      ∃ c : ConstructorVal, env.find? info.ctorName = some (.ctorInfo c) ∧ c.induct = S
  /-- The visible recursors. -/
  recursors : RecursorsCoherent safety env.constants venv
  /-- The major family of every present recursor is a header whose constructors are present. -/
  recursorMajorCtors : ∀ {name r}, env.find? name = some (.recInfo r) →
    ∃ info, env.find? r.getMajorInduct = some (.inductInfo info) ∧
      ∀ n ∈ info.ctors, ∃ ci, env.find? n = some ci
  /-- The ι rules of the visible recursors. -/
  iota : IotaRulesRegistered safety env venv
  /-- Once quotients are initialized, the quotient constants and the `Quot.lift` equation. -/
  quot : env.quotInit = true → QuotEnvCoherent env.constants venv

variable {venv : VEnv}

/-- `Quot.lift` has the recursor shape with five parameters, of which the first two are the
parameters of `Quot.mk`. -/
def QuotCoherent.liftRecursorShape (H : QuotCoherent venv) :
    VRecursorShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot [.param 0] where
  ctorParams_length := rfl
  ctorParams_closed := by
    intro p hp
    simp only [VExpr.bvarRange, List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    simp only [VExpr.ClosedN]
    omega
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
  rec_doms := by
    intro recDoms recBody hc hlen j hj
    rw [H.lift] at hc
    have htype : VExpr.wrapForalls H.liftRecursorShape.doms H.liftRecursorShape.result =
        VExpr.wrapForalls recDoms recBody := congrArg VConstant.type (Option.some.inj hc)
    obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by rw [hlen]; rfl) htype
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  ctor_doms := by
    intro ctorUvars ctorDoms ctorBody hc hlen i hi hd hcd
    rw [H.quotMk] at hc
    have htype : VExpr.wrapForalls H.mkConstructorShape.doms
          (VExpr.mkApps (.const ``Quot (VLevel.params 1))
            (VExpr.bvarRange 2 (2 + 1) ++ H.mkConstructorShape.indices)) =
        VExpr.wrapForalls ctorDoms ctorBody := congrArg VConstant.type (Option.some.inj hc)
    obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by rw [hlen]; rfl) htype
    match i, hi with
    | 0, _ => exact VEnv.IsDefEqU.refl ⟨_, .bvar (.succ (.succ (.succ (.succ .zero))))⟩

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
  have ⟨_, hsort⟩ := hq'.isType henv.orderedStrong hΓ
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
  have hcongr := VEnv.IsDefEq.mkApps_congr (args := [a1', a2', a3']) (args' := [α', r', a3'])
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

end Lean4Lean
