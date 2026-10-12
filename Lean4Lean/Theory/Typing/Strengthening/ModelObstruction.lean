import Lean4Lean.Theory.Typing.Strengthening.Model
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # Where the model route stops: class descent is `TypedFront`, reflection is false

Route B uses the observation model to descend a lifted equation. `Model.lean` shows that
`Q :: Γ ⊢ a↑ ≡ b↑` says exactly that `a` and `b` have the same observations in every target in
which `Q` is inhabited (`KEq.lift_iff`). To conclude `Γ ⊢ a ≡ b` one needs, in addition,

1. a passage from the inhabited targets to the target `Γ` itself (`ModelStrengthening`), and
2. **reflection**: agreement of observations in `Γ` gives a definitional equality.

This file pins both down for the ι pattern calculus.

* Reflection without a common type is false in every well-formed environment
  (`heterogeneous_reflection_false`: two proof variables of two different propositions have no
  observations at all, hence agree, and are not definitionally equal by unique typing).
* Reflection at a common lifted type (`FreshReflection`, the exact statement the route needs)
  is false in some well-formed environments with canonical `Eq`
  (`extension_not_freshReflection`): add three fresh axioms `I : Type`, `a b : I` to any such
  environment. Elements of a rigid non-structure type have no observations
  (`opaque_no_observations`: a rigid constant's observations are typed at observations of its
  type, which must be a sort or a `Π`, and `I` is neither), so `a` and `b` agree in every
  target; but both are stationary under full reduction, and `NormalEq` compares constants by
  name, so by confluence `a ≢ b` (`opaque_constants_not_defeq`). The model loses the identity of
  value constants of opaque types, and no finite-observation least fixed point can recover
  it without observing names, i.e. without becoming the term model.
* The declarative classes of the model are what a key of an observation carries. Descending
  element classes from `Q :: Γ` to `Γ` (`KeyFaithful`) is *equivalent* to the fixed-type
  strengthening statement `TypedFront` (`keyFaithful_iff_typedFront`), so the model's own data
  cannot be moved to the smaller target without the theorem being proved.

Consequently the model route reproduces the predecessor's obstruction in the new calculus: the
observations of a lifted term descend (they never depended on the source context), but the
*keys* in those observations are classes of the target, and the target must contain an
inhabitant of `Q`. No canonical-`Eq` hypothesis enters any statement of this file except the
confluence theorem used to separate the two opaque constants. -/

namespace Lean4Lean
namespace VEnv.StrengtheningModel
open VEnv _root_.Lean4Lean.VExpr VEnv.Model

variable {env : VEnv} {U : Nat}

/-! ## Class descent is the fixed-type front -/

/-- Transporting class-valued keys from `Q :: Γ` back to `Γ`: if the lifts of two terms of a
common type `T` have the same element class at `TyCls T↑` in `Q :: Γ`, the terms have the same
element class at `TyCls T` in `Γ`. -/
def KeyFaithful (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift =
      ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) b.lift →
    ElCls env U Γ (TyCls env U Γ T) a = ElCls env U Γ (TyCls env U Γ T) b

/-- The fixed-type front, stated inline (the shared definition `Strengthening.TypedFront` of
`TypingFront.lean` is this statement verbatim). -/
def TypedFront' (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEq U (Q :: Γ) a.lift b.lift T.lift → env.IsDefEq U Γ a b T

/-- Descending the model's classes is exactly the fixed-type front: a class equality in
`Q :: Γ` is one definitional equality there (`ElCls.collapse`) and conversely. -/
theorem keyFaithful_iff_typedFront (henv : env.WF) : KeyFaithful env ↔ TypedFront' env := by
  constructor
  · intro hk U Γ Q a b T hΓ hQ ha hb H
    have he := hk hΓ hQ ha hb (ElCls.eq_of_defeq TyCls.self H)
    have hm : ElCls env U Γ (TyCls env U Γ T) a b := by
      rw [he]; exact ElCls.self
    exact ElCls.collapse henv.orderedStrong hΓ ha TyCls.self hm
  · intro hf U Γ Q a b T hΓ hQ ha hb he
    have hm : ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift b.lift := by
      rw [he]; exact ElCls.self
    have H := ElCls.collapse henv.orderedStrong (show OnCtx (Q :: Γ) (env.IsType U) from ⟨hΓ, hQ⟩)
      (ha.weakN henv.ordered Ctx.LiftN.one) TyCls.self hm
    exact ElCls.eq_of_defeq TyCls.self (hf hΓ hQ ha hb H)

/-! ## Reflection without a common type is false -/

def propId : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
def propIdArrow : VExpr := .forallE propId propId.lift

theorem propId_typed (Γ : List VExpr) : env.HasType U Γ propId (.sort .zero) := by
  have hinner : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort (.imax .zero .zero)) := .forallE (.bvar .zero) (.bvar (.succ .zero))
  have hi : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort .zero) := .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
        ⟨trivial, trivial⟩ trivial rfl) hinner
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl) (HasType.forallE (HasType.sort trivial) hi)

theorem propIdArrow_typed (henv : env.Ordered) (Γ : List VExpr) :
    env.HasType U Γ propIdArrow (.sort .zero) := by
  have hp := propId_typed (env := env) (U := U) Γ
  exact .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl)
    (HasType.forallE hp (hp.weakN henv Ctx.LiftN.one))

/-- Even all targets and all valuations do not reflect heterogeneous proof equality: in the
context `[h₂ : propId → propId, h₁ : propId]`, the two variables have no observations and are
not definitionally equal (their types are not). The failure is unconditional for every
well-formed environment. -/
theorem heterogeneous_reflection_false (henv : env.WF) (U : Nat) :
    ∃ Γ a b P Q, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ a P ∧ env.HasType U Γ b Q ∧
      KEq env U Γ a b ∧ ¬ env.IsDefEqU U Γ a b := by
  let Γ := [propIdArrow, propId]
  have hΓ : OnCtx Γ (env.IsType U) :=
    ⟨⟨trivial, _, propId_typed []⟩, _, propIdArrow_typed henv.ordered [propId]⟩
  have ha : env.HasType U Γ (.bvar 1) propId := by
    simpa [Γ, propId, propIdArrow, VExpr.lift, VExpr.liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.succ (A := propIdArrow)
        (Lookup.zero (Γ := []) (ty := propId))))
  have hb : env.HasType U Γ (.bvar 0) propIdArrow := by
    simpa [Γ, propId, propIdArrow, VExpr.lift, VExpr.liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := [propId]) (ty := propIdArrow)))
  refine ⟨Γ, .bvar 1, .bvar 0, propId, propIdArrow, hΓ, ha, hb,
    KEq.proofs henv hΓ (propId_typed Γ) (propIdArrow_typed henv.ordered Γ) ha hb, ?_⟩
  intro H
  have htypes := (IsDefEqU.of_l henv hΓ H ha).uniqU henv hΓ hb
  obtain ⟨u, hd⟩ := (htypes.forallE_inv henv hΓ).1
  exact IsDefEqU.sort_forallE_inv henv hΓ ⟨_, hd⟩

/-! ## Reflection at a common lifted type: the statement the route needs -/

/-- Reflection of `KEq` for lifts at a common type in the extended context: the exact
semantic statement which, with `KEq.sound`, would give `Cancel`. Source terms need not be
typed below; their common type above may mention `Q`. -/
def FreshReflection (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄,
    OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) a.lift T →
    env.HasType U (Q :: Γ) b.lift T →
    KEq env U (Q :: Γ) a.lift b.lift →
    env.IsDefEqU U Γ a b

/-- `FreshReflection` gives the front form of strengthening directly (soundness above,
reflection below). -/
theorem front_of_freshReflection (henv : env.WF) (hr : FreshReflection env)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U)) (H : env.IsDefEqU U (Q :: Γ) a.lift b.lift) :
    env.IsDefEqU U Γ a b := by
  obtain ⟨T, H⟩ := H
  exact hr hΓ H.hasType.1 H.hasType.2 (KEq.sound henv hΓ ⟨T, H⟩)

/-! ## Opaque constants have no observations -/

/-- Registration conditions of an opaque constant: rigid, not a constructor, not the
constructor of a projection-registered family, not such a family. Fresh axioms satisfy them
(`opaque_of_absent`). -/
structure OpaqueHead (env : VEnv) (c : Name) : Prop where
  rigid : env.Rigid c
  notCtor : ¬ IsCtor env c
  notProjCtor : ¬ IsProjCtor env c
  notFamily : ∀ info, ¬ env.projections c info

/-- A rigid spine observation typed at observations of a rigid spine: impossible, since the
rigid-spine clause needs a `sort` or `piDom` observation of the type. -/
theorem rigid_typed_wrap_absurd {Δ : List VExpr}
    {I c : Name} {ls lsI : List VLevel} {args : List VExpr}
    {τs : List Ob} {cv : VExpr → Prop} {keys : List Key} {r : Ob}
    (hI : env.Rigid I)
    (hτ : ∀ τ ∈ τs, Obs env U Δ .id .empty (.mkApps (.const I lsI) args) τ)
    (ht : TypedOb env U Δ cv (wrap keys r) τs)
    (hr : RigidEnd c (ls.map (·.eval)) keys r) : False := by
  cases keys with
  | nil =>
    rcases hr with ⟨s, rfl⟩ | ⟨i, hi, _⟩ | ⟨i, hi, _⟩
    · cases ht with
      | rigid hm => exact rigid_spine_not_pi hI (hτ _ hm) (.inl ⟨_, rfl⟩)
    · simp at hi
    · simp at hi
  | cons key keys =>
    cases ht with
    | app hm => exact rigid_spine_not_pi hI (hτ _ hm) (.inr (.inl ⟨_, rfl⟩))

/-- An opaque constant of a rigid type has no observation, in any target and at any
valuation. -/
theorem opaque_no_observations {Δ : List VExpr}
    {σ : VExpr.Subst} {S : ObSets} {c I : Name} {ls lsI : List VLevel}
    {ci : VConstant} {args : List VExpr}
    (hc : OpaqueHead env c) (hI : env.Rigid I)
    (hci : env.constants c = some ci)
    (hty : ci.type.instL ls = .mkApps (.const I lsI) args)
    {o : Ob} (h : Obs env U Δ σ S (.const c ls) o) : False := by
  cases h with
  | const _ hci' hτ ht hr =>
    have ee := Option.some.inj (hci'.symm.trans hci)
    subst_vars
    exact rigid_typed_wrap_absurd hI (by simpa [hty] using hτ) ht hr
  | delta hdf hlhs =>
    exact hc.rigid.defeqs _ hdf _ (by rw [hlhs]; rfl)
  | ctor hctor => exact hc.notCtor hctor
  | projCtor hp hn => exact hc.notProjCtor ⟨_, _, hp, hn⟩
  | famTy _ _ hp => exact hc.notFamily _ hp
  | famDom _ _ hp => exact hc.notFamily _ hp
  | rule hdf hlhs =>
    exact hc.rigid.defeqs _ hdf _ (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head)
  | pat hp => exact hc.rigid.pats _ _ hp (SimplePattern.iota_headConst ..)

/-- The all-target model identifies any two opaque inhabitants of one rigid type. -/
theorem opaque_KEq {Γ : List VExpr}
    {a b I : Name} {lsA lsB lsI : List VLevel}
    {ciA ciB : VConstant} {args : List VExpr}
    (ha : OpaqueHead env a) (hb : OpaqueHead env b) (hI : env.Rigid I)
    (hca : env.constants a = some ciA) (hcb : env.constants b = some ciB)
    (hA : ciA.type.instL lsA = .mkApps (.const I lsI) args)
    (hB : ciB.type.instL lsB = .mkApps (.const I lsI) args) :
    KEq env U Γ (.const a lsA) (.const b lsB) := by
  intro Δ σ S _ _ _
  constructor
  · intro o ho
    exact False.elim (opaque_no_observations ha hI hca hA ho)
  · intro o ho
    exact False.elim (opaque_no_observations hb hI hcb hB ho)

/-! ## Opaque constants are separated by confluence -/

/-- Inhabitants of an opaque non-structure `Type` are neither functions, proofs nor structure
inhabitants, by unique typing and head inversion. -/
theorem opaque_type_exclusions (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hr : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (hI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (he : env.HasType U Γ e (.const I lsI)) :
    (∀ A B, ¬ env.HasType U Γ e (.forallE A B)) ∧
    (∀ P, env.HasType U Γ P (.sort .zero) → ¬ env.HasType U Γ e P) ∧
    (∀ family info levels args, env.projections family info →
      ¬ env.HasType U Γ e (.mkApps (.const family levels) args)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hf
    exact IsDefEqU.rigidApp_forallE_inv (args := []) henv hΓ hr hI (he.uniqU henv hΓ hf)
  · intro P hP hp
    have hIP := (he.uniqU henv hΓ hp).of_r henv hΓ hP
    have hl := (hI.uniqU henv hΓ hIP.hasType.1).sort_inv henv hΓ
    have hz := congrFun hl []
    simp [VLevel.eval] at hz
  · intro family info levels args hf hs
    have hne : I ≠ family := by intro hh; subst family; exact hn info hf
    exact IsDefEqU.rigidApp_ne (args := []) henv hΓ hr (henv.projectionRigid hf)
      hne hI (he.uniqU henv hΓ hs)

section
open Params
variable [Params]

def NonFunctionNonProof (Γ : List VExpr) (e : VExpr) : Prop :=
  (∀ A B, ¬ Params.env.HasType univs Γ e (.forallE A B)) ∧
  (∀ P, Params.env.HasType univs Γ P (.sort .zero) → ¬ Params.env.HasType univs Γ e P)

/-- No full reduction leaves the term. -/
def Stationary (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ t, FullReduction Γ e t → t = e

theorem normalEq_const_name {Γ : List VExpr} {a b : Name} {lsA lsB : List VLevel}
    (ha : NonFunctionNonProof Γ (.const a lsA))
    (h : NormalEq Γ (.const a lsA) (.const b lsB)) : a = b := by
  obtain ⟨n, hn⟩ := h
  cases hn with
  | refl => rfl
  | constDF => rfl
  | etaBoth ht => exact False.elim (ha.1 _ _ ht)
  | proofIrrel hp ht => exact False.elim (ha.2 _ hp ht)

theorem parRed_const_stable {Γ : List VExpr} {c : Name} {ls : List VLevel}
    (hr : Params.env.Rigid c) {t : VExpr} (h : ParRed Γ (.const c ls) t) :
    t = .const c ls := by
  generalize he : VExpr.const c ls = e at h
  cases h with
  | const => cases he; rfl
  | extra hp hm =>
    exact False.elim (Params.not_rigid_match hr hp hm (by rw [← he]; rfl))
  | _ => cases he

theorem fullStep_const_stable {Γ : List VExpr} {c : Name} {ls : List VLevel}
    (hr : Params.env.Rigid c) (hreg : recursorData c = none) (hq : c ≠ ``Quot.lift)
    (hf : ∀ A B, ¬ Params.env.HasType univs Γ (.const c ls) (.forallE A B))
    (hs : ∀ family info levels args, Params.env.projections family info →
      ¬ Params.env.HasType univs Γ (.const c ls) (.mkApps (.const family levels) args))
    {t : VExpr} (h : FullStep Γ (.const c ls) t) : t = .const c ls := by
  generalize he : VExpr.const c ls = e at h
  cases h with
  | core h => subst e; exact parRed_const_stable hr h
  | delta h =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [VExpr.spine_mkApps_exact _ _ rfl] at hh
    simp only [VExpr.getAppFnArgs] at hh
    cases hh
    cases h with
    | intro hl => simp [hreg] at hl
  | quotDelta =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [VExpr.spine_mkApps_exact _ _ rfl] at hh
    simp only [VExpr.getAppFnArgs] at hh
    cases hh
    exact False.elim (hq rfl)
  | structEta hp _ _ ht => subst e; exact False.elim (hs _ _ _ _ hp ht)
  | funEta ht => subst e; exact False.elim (hf _ _ ht)
  | _ => cases he

theorem stationary_of_step_stable {Γ : List VExpr} {e : VExpr}
    (hs : ∀ t, FullStep Γ e t → t = e) : Stationary Γ e := by
  intro t h
  induction h with
  | rfl => rfl
  | tail h hstep ih => subst_vars; exact hs _ hstep

end

/-- Confluence separates distinct stationary constants that are neither functions nor
proofs. -/
theorem stationary_constants_not_defeq (henv : env.WF)
    (heq : env.HasCanonicalEq) {Γ : List VExpr}
    {a b : Name} {lsA lsB : List VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (hne : a ≠ b)
    (ha : @NonFunctionNonProof (henv.params U) Γ (.const a lsA))
    (hsa : @Stationary (henv.params U) Γ (.const a lsA))
    (hsb : @Stationary (henv.params U) Γ (.const b lsB)) :
    ¬ env.IsDefEqU U Γ (.const a lsA) (.const b lsB) := by
  intro ⟨T, H⟩
  letI := henv.params U
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  cases hsa x hx
  cases hsb y hy
  exact hne (normalEq_const_name ha hn)

/-- A rigid constant is not in the recursor registry. -/
theorem recursorRegistry_eq_none_of_rigid (hr : env.Rigid c) : env.recursorRegistry c = none :=
  recursorRegistry_none fun _ h => h.not_rigid hr

theorem opaque_stationary (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {c I : Name} {ls lsI : List VLevel}
    (hc : env.Rigid c) (hq : c ≠ ``Quot.lift)
    (hI : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (htI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (htc : env.HasType U Γ (.const c ls) (.const I lsI)) :
    @Stationary (henv.params U) Γ (.const c ls) := by
  letI := henv.params U
  obtain ⟨hf, _, hs⟩ := opaque_type_exclusions henv hΓ hI hn htI htc
  apply stationary_of_step_stable
  intro t ht
  exact fullStep_const_stable hc (recursorRegistry_eq_none_of_rigid hc) hq hf hs ht

/-- Two distinct rigid constants of one rigid non-structure `Type` are not definitionally
equal (canonical `Eq` enters only through the confluence theorem). -/
theorem opaque_constants_not_defeq (henv : env.WF)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U))
    {a b I : Name} {lsA lsB lsI : List VLevel}
    (ha : env.Rigid a) (hb : env.Rigid b) (hI : env.Rigid I)
    (hn : ∀ info, ¬ env.projections I info)
    (hne : a ≠ b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift)
    (htI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (hta : env.HasType U Γ (.const a lsA) (.const I lsI))
    (htb : env.HasType U Γ (.const b lsB) (.const I lsI)) :
    ¬ env.IsDefEqU U Γ (.const a lsA) (.const b lsB) := by
  obtain ⟨hf, hp, _⟩ := opaque_type_exclusions henv hΓ hI hn htI hta
  exact stationary_constants_not_defeq henv heq hΓ hne ⟨hf, hp⟩
    (opaque_stationary henv hΓ ha haq hI hn htI hta)
    (opaque_stationary henv hΓ hb hbq hI hn htI htb)

/-- In an environment with two opaque constants of an opaque type, `FreshReflection` fails. -/
theorem opaque_not_freshReflection (henv : env.WF)
    (heq : env.HasCanonicalEq) {a b I : Name} {ciA ciB : VConstant}
    (ha : OpaqueHead env a) (hb : OpaqueHead env b) (hI : env.Rigid I)
    (hn : ∀ info, ¬ env.projections I info)
    (hne : a ≠ b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift)
    (hca : env.constants a = some ciA) (hcb : env.constants b = some ciB)
    (hA : ciA.type.instL [] = .const I [])
    (hB : ciB.type.instL [] = .const I [])
    (htI : env.HasType 0 [] (.const I []) (.sort (.succ .zero)))
    (hta : env.HasType 0 [] (.const a []) (.const I []))
    (htb : env.HasType 0 [] (.const b []) (.const I [])) :
    ¬ FreshReflection env := by
  intro hF
  have hK : KEq env 0 [.sort .zero] (VExpr.const a []).lift (VExpr.const b []).lift :=
    opaque_KEq (args := []) ha hb hI hca hcb hA hB
  have he := hF (Q := .sort .zero) (Γ := []) ⟨trivial, _, .sort trivial⟩
    (hta.weakN henv.ordered Ctx.LiftN.one) (htb.weakN henv.ordered Ctx.LiftN.one) hK
  exact opaque_constants_not_defeq (Γ := []) henv heq trivial ha.rigid hb.rigid hI hn
    hne haq hbq htI hta htb he

/-! ## Three fresh axioms realise the opaque heads -/

/-- Add an axiom `c : T` (universe-monomorphic) to the constant table. -/
def addAxiom (env : VEnv) (c : Name) (T : VExpr) : VEnv :=
  { env with constants := fun n => if c = n then some ⟨0, T⟩ else env.constants n }

theorem addAxiom_installed (fresh : env.constants c = none) :
    env.addConst c ⟨0, T⟩ = some (addAxiom env c T) := by
  simp [VEnv.addConst, fresh, addAxiom]

theorem addAxiom_wf (henv : env.WF) (fresh : env.constants c = none)
    (ht : env.IsType 0 [] T) : (addAxiom env c T).WF := by
  obtain ⟨ds, hds⟩ := henv
  exact ⟨.axiom ⟨⟨0, T⟩, c⟩ :: ds, .decl (.axiom ht (addAxiom_installed fresh)) hds⟩

theorem addAxiom_le (fresh : env.constants c = none) : env ≤ addAxiom env c T := by
  refine ⟨fun h => ?_, id, id, id⟩
  simp only [addAxiom]
  split
  · rename_i hc; subst hc; rw [fresh] at h; cases h
  · exact h

@[simp] theorem addAxiom_constants_self : (addAxiom env c T).constants c = some ⟨0, T⟩ := by
  simp [addAxiom]

theorem addAxiom_constants_ne (h : c ≠ n) : (addAxiom env c T).constants n = env.constants n := by
  simp [addAxiom, h]

theorem addAxiom_constants_none (fresh : env.constants n = none) (h : c ≠ n) :
    (addAxiom env c T).constants n = none := by
  rw [addAxiom_constants_ne h, fresh]

/-- The extension by `I : Type`, `a : I`, `b : I`. -/
def extension (env : VEnv) (I a b : Name) : VEnv :=
  addAxiom (addAxiom (addAxiom env I (.sort (.succ .zero))) a (.const I []))
    b (.const I [])

/-- Names absent from the constant table and pairwise distinct. -/
structure FreshNames (env : VEnv) (I a b : Name) : Prop where
  freshI : env.constants I = none
  freshA : env.constants a = none
  freshB : env.constants b = none
  IA : I ≠ a
  IB : I ≠ b
  AB : a ≠ b

theorem extension_properties (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : FreshNames env I a b) :
    (extension env I a b).WF ∧
    (extension env I a b).HasCanonicalEq ∧
    (extension env I a b).constants I = some ⟨0, .sort (.succ .zero)⟩ ∧
    (extension env I a b).constants a = some ⟨0, .const I []⟩ ∧
    (extension env I a b).constants b = some ⟨0, .const I []⟩ := by
  have freshA : (addAxiom env I (.sort (.succ .zero))).constants a = none :=
    addAxiom_constants_none hf.freshA hf.IA
  have freshB : (addAxiom (addAxiom env I (.sort (.succ .zero))) a (.const I [])).constants b =
      none :=
    addAxiom_constants_none (addAxiom_constants_none hf.freshB hf.IB) hf.AB
  have hw1 := addAxiom_wf henv hf.freshI (T := .sort (.succ .zero)) ⟨_, HasType.sort trivial⟩
  have hI : (addAxiom env I (.sort (.succ .zero))).HasType 0 []
      (.const I []) (.sort (.succ .zero)) := by
    simpa [VExpr.instL, VLevel.inst] using HasType.const (U := 0) (Γ := []) (ls := [])
      (addAxiom_constants_self (env := env) (c := I) (T := .sort (.succ .zero))) (by simp) rfl
  have hw2 := addAxiom_wf hw1 freshA ⟨_, hI⟩
  have hI2 := hI.mono (addAxiom_le (T := .const I []) freshA)
  refine ⟨addAxiom_wf hw2 freshB ⟨_, hI2⟩,
    heq.mono ((addAxiom_le hf.freshI).trans ((addAxiom_le freshA).trans (addAxiom_le freshB))),
    ?_, ?_, ?_⟩
  · rw [extension, addAxiom_constants_ne (Ne.symm hf.IB), addAxiom_constants_ne (Ne.symm hf.IA)]
    exact addAxiom_constants_self
  · rw [extension, addAxiom_constants_ne (Ne.symm hf.AB)]
    exact addAxiom_constants_self
  · exact addAxiom_constants_self

/-- Opaque heads depend only on the rules, patterns and projection entries. -/
theorem OpaqueHead.of_eq {env' : VEnv} (h : OpaqueHead env c) (hd : env'.defeqs = env.defeqs)
    (hp : env'.pats = env.pats) (hpr : env'.projections = env.projections) :
    OpaqueHead env' c := by
  refine ⟨h.rigid.of_eq hd hp, fun hc => h.notCtor ?_, fun hc => h.notProjCtor ?_,
    fun info hi => h.notFamily info (by rwa [hpr] at hi)⟩
  · rcases hc with ⟨df, hdf, hm⟩ | ⟨p, r, recN, M, N, hpat, he⟩
    · exact .inl ⟨df, by rwa [hd] at hdf, hm⟩
    · exact .inr ⟨p, r, recN, M, N, by rwa [hp] at hpat, he⟩
  · obtain ⟨fam, info, hi, hn⟩ := hc
    exact ⟨fam, info, by rwa [hpr] at hi, hn⟩

/-- The rules of the extension are those of `env`. -/
theorem extension_opaque (h : OpaqueHead env c) : OpaqueHead (extension env I a b) c :=
  h.of_eq rfl rfl rfl

/-- A name absent from a well-formed environment heads no rule, is no constructor and no
projection family. -/
theorem opaque_of_absent (henv : env.WF) (fresh : env.constants c = none) :
    OpaqueHead env c := by
  refine ⟨henv.rigid_of_absent fresh, ?_, ?_, ?_⟩
  · rintro (hc | hc)
    · obtain ⟨rfl, hq⟩ := henv.installedCtor_eq hc
      obtain ⟨-, hmk, -⟩ := henv.quotConsts hq
      rw [fresh] at hmk; cases hmk
    · obtain ⟨p, r, recN, M, N, hp, rfl⟩ := hc
      obtain ⟨ci, hci, -⟩ := henv.patsIota.ctor_shape hp
      rw [fresh] at hci; cases hci
  · rintro ⟨fam, info, hp, rfl⟩
    have hi := henv.ordered.projectionConstructor hp
    rw [fresh] at hi; cases hi
  · intro info hp
    obtain ⟨decl, type, ctor, _, _, _, _, _, _, _, _, _, _, hi, _⟩ :=
      henv.ordered.projectionShape hp
    rw [fresh] at hi; cases hi

theorem extension_opaque_heads (henv : env.WF) (hf : FreshNames env I a b) :
    OpaqueHead (extension env I a b) I ∧
    OpaqueHead (extension env I a b) a ∧
    OpaqueHead (extension env I a b) b :=
  ⟨extension_opaque (opaque_of_absent henv hf.freshI),
   extension_opaque (opaque_of_absent henv hf.freshA),
   extension_opaque (opaque_of_absent henv hf.freshB)⟩

/-- **`FreshReflection` fails.** Every well-formed environment with canonical `Eq` extends, by
three fresh axioms `I : Type`, `a b : I`, to a well-formed environment with canonical `Eq` in
which the all-target observation model identifies the two definitionally distinct constants
`a`, `b` at the common type `I`. So the reflection step of the model route is unavailable. -/
theorem extension_not_freshReflection (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : FreshNames env I a b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift) :
    (extension env I a b).WF ∧ (extension env I a b).HasCanonicalEq ∧
    ¬ FreshReflection (extension env I a b) := by
  obtain ⟨hw, he, hI, ha, hb⟩ := extension_properties henv heq hf
  obtain ⟨hOI, hOA, hOB⟩ := extension_opaque_heads henv hf
  refine ⟨hw, he, ?_⟩
  apply opaque_not_freshReflection hw he hOA hOB hOI.rigid hOI.notFamily
    hf.AB haq hbq ha hb rfl rfl
  · simpa [VExpr.instL, VLevel.inst] using
      HasType.const (U := 0) (Γ := []) (ls := []) hI (by simp) rfl
  · simpa [VExpr.instL] using HasType.const (U := 0) (Γ := []) (ls := []) ha (by simp) rfl
  · simpa [VExpr.instL] using HasType.const (U := 0) (Γ := []) (ls := []) hb (by simp) rfl

/-- Fresh names always exist: `FreshReflection` fails in some extension of every well-formed
environment with canonical `Eq`. -/
theorem exists_not_freshReflection (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : FreshNames env I a b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift) :
    ∃ env' : VEnv, env ≤ env' ∧ env'.WF ∧ env'.HasCanonicalEq ∧ ¬ FreshReflection env' :=
  let ⟨hw, he, hr⟩ := extension_not_freshReflection henv heq hf haq hbq
  ⟨_, (addAxiom_le hf.freshI).trans ((addAxiom_le (addAxiom_constants_none hf.freshA hf.IA)).trans
    (addAxiom_le (addAxiom_constants_none (addAxiom_constants_none hf.freshB hf.IB) hf.AB))),
    hw, he, hr⟩

end VEnv.StrengtheningModel
end Lean4Lean
