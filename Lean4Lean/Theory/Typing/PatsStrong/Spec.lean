import Lean4Lean.Theory.Typing.PatsStrong.ConstExt
import Lean4Lean.Theory.Typing.PatsStrong.Telescope
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! # The interfaces of the `patsStrong` proof

This file states, with no proofs of its own, the facts the history induction
(`PatsStrong/History.lean`) and the per-rule argument (`PatsStrong/Rule.lean`) consume:

* `StrongHeadInversion env`: head inversion **on strong derivations with strong
  conclusions** — the wave-1C target. Its three clauses are the strong forms of the branch's
  `HeadInversion.sort_sort`, `forallE_forallE` and `former_args`
  (`Theory/Typing/HeadInversionDefs.lean`). The branch's model proves these with *weak*
  conclusions (`ElCls.collapse` returns an `IsDefEq`); the `patsStrong` argument needs the
  conclusions in the strong system, because the reduct's typing is built by instantiating the
  generic rule with the actual arguments and the fields' types depend on the parameters: the
  field `f : Fields(cp)` of the constructor spine must be retyped at `Fields(p)` of the
  recursor spine, which is a `defeqDF` by a *strong* `cp ≡ p`. A weak `cp ≡ p` cannot be
  strengthened at this point: that is the obligation itself.
* `IotaRuleData`, `IotaRuleData.GenericStrong`: an ι rule read off a recursor rule, and its
  generic instance strongly typed in the telescope context of its holes (recursor parameters,
  motives, minors, then constructor fields). This is the form in which the rule's typing must
  be carried along the history (`Stage.rules`): it is established at the stage-2 environment
  `envR` of the declaring `addInduct` — a constant-only extension of a *strict* prefix, where
  `PatsStrongOn envR` is available from the induction — and moved to later environments by
  `IsDefEqStrong.mono`. This is the cut of the circle.
* `Stage env`: the per-environment invariant: `Ordered`, `EnvStrong`, every registered rule
  carries `GenericStrong` and its syntactic shape, and the type formers it eliminates are
  rigid. **It does not contain `PatsStrongOn env`.** `PatsStrongOn env` is *derived* from
  `Stage env` and `StrongHeadInversion env` by the per-rule argument, and `StrongHeadInversion
  env` must in turn be proved from `Stage env` alone (`Wave1C`): that is the no-circularity
  condition, visible in the hypotheses.
-/

namespace Lean4Lean

/-- The head constant of a simple pattern: the recursor of an ι rule, the constant of a δ rule. -/
def SimplePattern.head : SimplePattern → Name
  | .iota r _ _ _ => r
  | .defn c => c

theorem SimplePattern.toPattern_head_eq : ∀ sp : SimplePattern,
    ∃ n, sp.toPattern = Pattern.varN (.const sp.head) n ∨
      ∃ n' c, sp.toPattern = .app (Pattern.varN (.const sp.head) n) (Pattern.varN (.const c) n')
  | .iota r m c n => ⟨m, .inr ⟨n, c, rfl⟩⟩
  | .defn c => ⟨0, .inl rfl⟩

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## Chains and spines in the strong system -/

/-- A chain of strong sort-typed equalities: the strong counterpart of the branch's
`TypeChain`. Two typings of one term are related by such a chain, not by one equality, until
the sort levels are reconciled (`sort_sort`). -/
inductive TypeChainS (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop
  | single : (∃ u, env.IsDefEqStrong U Γ X Y (.sort u)) → TypeChainS env U Γ X Y
  | tail : TypeChainS env U Γ X Y → (∃ u, env.IsDefEqStrong U Γ Y Z (.sort u)) →
    TypeChainS env U Γ X Z

/-- Pairwise strong equality of two argument spines along a Π-telescope `T`: the strong
counterpart of the branch's `SpineArgsEq`. -/
inductive SpineArgsEqS (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → List VExpr → Prop
  | nil : SpineArgsEqS env U Γ T [] []
  | cons : env.IsDefEqStrong U Γ a a' A → SpineArgsEqS env U Γ (B.inst a) as as' →
    SpineArgsEqS env U Γ (.forallE A B) (a :: as) (a' :: as')

/-- No rule of `env` is headed by `c`: no definitional axiom's left-hand side and no
registered pattern has `c` as its head constant. Type formers of inductive blocks are rigid
in every well-formed environment and in its constant-only extensions. -/
def Rigid (env : VEnv) (c : Name) : Prop :=
  (∀ df, env.defeqs df → ∀ us, df.lhs.getAppFn ≠ .const c us) ∧
  ∀ p r, env.pats p r → ∀ sp : SimplePattern, p = sp.toPattern → sp.head ≠ c

/-! ## Head inversion on strong derivations -/

/-- **Head inversion on strong derivations, with strong conclusions.** The wave-1C target of the
port. The clauses are the strong forms of the branch's `HeadInversion` (the clauses the
`patsStrong` argument uses; separation clauses are not needed):

* `sort_sort`: two sorts related by a chain have equivalent levels;
* `forallE_forallE`: Π-injectivity, with strong equalities of domain and codomain;
* `former_args`: two applications of a rigid constant related by a chain have equivalent
  level lists and pairwise strongly equal arguments along the constant's type.

Stated for an arbitrary environment; the history induction asks for it at every `Stage`
environment (`Wave1C`). The branch's `Injectivity.lean`/`UniqueTyping.lean` state the weak
forms and are `sorry` on master and in #43; the branch's model proves the weak forms. -/
structure StrongHeadInversion (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, CtxStrong env U Γ →
    TypeChainS env U Γ (.sort u) (.sort v) → u ≈ v
  forallE_forallE : ∀ {U Γ A B A' B'}, CtxStrong env U Γ →
    TypeChainS env U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEqStrong U Γ A A' (.sort u)) ∧ ∃ v, env.IsDefEqStrong U (A :: Γ) B B' (.sort v)
  former_args : ∀ {U Γ c ci ls ls' args args'}, CtxStrong env U Γ →
    env.Rigid c → env.constants c = some ci →
    TypeChainS env U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    List.Forall₂ (· ≈ ·) ls ls' ∧ SpineArgsEqS env U Γ (ci.type.instL ls) args args'

/-! ## An ι rule and its generic typing -/

/-- An ι rule as `addRecRule` registers it, for a direct block (`ctorParams = numParams`):
recursor `rec` with `np` parameters, `nm` motives, `nmin` minors and `nind` indices, firing
on `ctor` with `nf` fields, reduct template `rhs`. -/
structure IotaRuleData where
  recName : Name
  np : Nat
  nm : Nat
  nmin : Nat
  nind : Nat
  ctorName : Name
  nf : Nat
  rhs : VExpr
  hrhs : rhs.Closed

namespace IotaRuleData

/-- The parameters/motives/minors prefix of the recursor spine. -/
@[reducible] def k (D : IotaRuleData) : Nat := D.np + D.nm + D.nmin

/-- The pattern `addRecRule` registers. -/
@[reducible] def pattern (D : IotaRuleData) : Pattern :=
  (SimplePattern.iota D.recName (D.np + D.nm + D.nmin + D.nind) D.ctorName (D.np + D.nf)).toPattern

/-- The reduct and check `addRecRule` registers. -/
def rhsR (D : IotaRuleData) : D.pattern.RHS × D.pattern.Check :=
  (SimplePattern.iotaRHS D.recName D.ctorName D.np D.nm D.nmin D.nind D.np D.nf D.rhs D.hrhs, .true)

/-- The rule of recursor `r` for rule `ru`, as `addRecRule` reads it. -/
def ofRule (r : VRecursor) (ru : VRecRule) (hc : ru.rhs.Closed) (_hp : ru.ctorParams = r.numParams) :
    IotaRuleData :=
  ⟨r.name, r.numParams, r.numMotives, r.numMinors, r.numIndices, ru.ctor, ru.nfields, ru.rhs, hc⟩

/-- The generic redex: the recursor at the identity level instantiation applied to the
telescope variables of its parameters, motives and minors, to index terms `idx`, and to the
constructor (at levels `cls`) applied to parameter terms `cpar` and the field variables. The
holes the reduct does not use (`idx`, `cls`, `cpar`) are arbitrary terms over the context, as
in `VEnv.PatTyped`; a well-typed generic instance has `cpar` the parameter variables and `idx`
the constructor's result indices. -/
def genericRedex (D : IotaRuleData) (U : Nat) (idx : List VExpr) (cls : List VLevel)
    (cpar : List VExpr) : VExpr :=
  (VExpr.const D.recName (VLevel.params U)).mkApps
    (VExpr.bvarsDesc D.nf D.k ++ idx ++
      [(VExpr.const D.ctorName cls).mkApps (cpar ++ VExpr.bvarsDesc 0 D.nf)])

/-- The generic reduct: the template applied to all telescope variables. -/
def genericReduct (D : IotaRuleData) : VExpr :=
  D.rhs.mkApps (VExpr.bvarsDesc 0 (D.k + D.nf))

/-- The generic instance of the rule, strongly typed in its telescope context `doms`
(outermost domain first; `doms.reverse` is the de Bruijn context). -/
def GenericStrong (env : VEnv) (D : IotaRuleData) : Prop :=
  ∃ (U : Nat) (doms idx cpar : List VExpr) (cls : List VLevel) (B : VExpr),
    doms.length = D.k + D.nf ∧ idx.length = D.nind ∧ cpar.length = D.np ∧
    CtxStrong env U doms.reverse ∧
    env.IsDefEqStrong U doms.reverse (D.genericRedex U idx cls cpar) (D.genericRedex U idx cls cpar) B ∧
    env.IsDefEqStrong U doms.reverse D.genericReduct D.genericReduct B

/-- The same generic instance typed in the weak system: what the rule installer (our
`Verify/Inductive/Rules/EquationWF.lean`, PORT_PLAN §2.3) supplies at the stage-2
environment of the declaring block. It implies #43's `VEnv.PatTyped` (`GenericWeak.patTyped`,
`Rule.lean`) and is strengthened to `GenericStrong` by `IsDefEq.strong'` at that
environment. -/
def GenericWeak (env : VEnv) (D : IotaRuleData) : Prop :=
  ∃ (U : Nat) (doms idx cpar : List VExpr) (cls : List VLevel) (B : VExpr),
    doms.length = D.k + D.nf ∧ idx.length = D.nind ∧ cpar.length = D.np ∧
    OnCtx doms.reverse (env.IsType U) ∧
    env.HasType U doms.reverse (D.genericRedex U idx cls cpar) B ∧
    env.HasType U doms.reverse D.genericReduct B

/-- The syntactic shape of the rule's constants in `env`: the recursor's type has the
recursor telescope (`RecShape`) and eliminates the type former `T`; the constructor's type
returns `T` applied to its parameters and `nind` indices (`CtorResult`); `T` is rigid. All of
it is read off `VInductDecl.WF` at the declaring step (`rec_shape`, `rules_ctor`); constants
never change afterwards, and rigidity of `T` is preserved by every later well-formed step
(`Rigid.step`, `History.lean`). -/
structure ShapeAt (env : VEnv) (D : IotaRuleData) (T : Name) : Prop where
  rec_find : ∃ recC, env.constants D.recName = some recC ∧
    recC.type.RecShape D.np D.nm D.nmin D.nind ∧
    recC.type.majorFormer? (D.np + D.nm + D.nmin + D.nind) = some T
  ctor_find : ∃ ctorC, env.constants D.ctorName = some ctorC ∧
    ctorC.type.CtorResult T D.np D.nf D.nind
  rigid : env.Rigid T

/-- `ShapeAt` for the type former the rule eliminates. -/
def Shape (env : VEnv) (D : IotaRuleData) : Prop := ∃ T, D.ShapeAt env T

theorem GenericStrong.mono {env env' : VEnv} (hle : env ≤ env') {D : IotaRuleData}
    (h : D.GenericStrong env) : D.GenericStrong env' := by
  obtain ⟨U, doms, idx, cpar, cls, B, h1, h2, h3, hΓ, he, hr⟩ := h
  exact ⟨U, doms, idx, cpar, cls, B, h1, h2, h3,
    hΓ.mono fun ⟨u, h⟩ => ⟨u, h.mono hle⟩, he.mono hle, hr.mono hle⟩

end IotaRuleData

/-! ## The per-stage invariant -/

/-- The invariant carried along the history. `PatsStrongOn env` is deliberately absent: it is
derived from this and `StrongHeadInversion env` (`Rule.lean`). -/
structure Stage (env : VEnv) : Prop where
  ordered : Ordered env
  strong : OnTypes env (EnvStrong env)
  /-- Every registered rule is an ι rule of a direct block, carries the strong typing of its
  generic instance, and has its constants in shape. -/
  rules : ∀ {p : Pattern} {r : p.RHS × p.Check}, env.pats p r →
    ∃ D : IotaRuleData, ∃ e : p = D.pattern, e ▸ r = D.rhsR ∧ D.GenericStrong env ∧ D.Shape env

/-- **The wave-1C obligation, as the history induction consumes it**: head inversion with
strong conclusions in every `Stage` environment, from the `Stage` data alone — without
`PatsStrongOn env` and hence without `IsDefEq.strong` at `env`. The branch's model consumes
strong derivations (`Model.SoundEnv`) and emits weak conclusions; the upgrade to strong
conclusions (strong observation classes or an equivalent) is the open research item of this
route. -/
def Wave1C : Prop := ∀ {env : VEnv}, Stage env → StrongHeadInversion env

/-- **The rule installer's obligation** (wave 1B / PORT_PLAN §2.3): every rule of a well-formed
block, read as `IotaRuleData`, is generically typed in the weak system at the stage-2
environment, and the block's constants have the shape `Shape` records there. On #43 this is
`VInductDecl.WF.rules_wf` (`VEnv.PatTyped`, which fixes the generic context only up to a
bijection of the holes) and `rec_shape`/`rules_ctor`; the port replaces `rules_wf` by the
telescope-literal form the branch's `EquationWF.lean` produces, which is what is stated here. -/
def RulesGenericTyped : Prop :=
  ∀ {env envR : VEnv} {decl : VInductDecl}, decl.WF env → decl.addTypesCtorsRecs env = some envR →
    ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∀ (hc : ru.rhs.Closed) (hp : ru.ctorParams = r.numParams),
      (IotaRuleData.ofRule r ru hc hp).GenericWeak envR ∧
      (IotaRuleData.ofRule r ru hc hp).Shape envR

end VEnv
end Lean4Lean
