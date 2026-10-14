import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaEnvironment
import Lean4Lean.Theory.Typing.Confluence.WFParams
import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Finite recursive-type separation

A recursive type whose unfolding retains itself down the left domain of Pis
retains that constant along every finite full reduction. Normal equality of
sort-typed results preserves the same left-domain marker. This tests finite
conversion, rather than equality of infinite unfolding trees.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Following Pi domains eventually reaches the marked constant. Bodies are
unrestricted, so reductions within them do not affect this invariant. -/
inductive RecursiveTypeShape (c : Name) : VExpr → Prop where
  | const : RecursiveTypeShape c (.const c ls)
  | forallE : RecursiveTypeShape c A → RecursiveTypeShape c (.forallE A B)

/-- A finite expression has at most one left-domain marker. -/
theorem RecursiveTypeShape.unique (H : RecursiveTypeShape c e) (H' : RecursiveTypeShape d e) :
    c = d := by
  induction H with
  | const => cases H'; rfl
  | forallE _ ih => cases H' with | forallE H' => exact ih H'

/-- A constant spine with this shape is the bare marked constant. -/
theorem RecursiveTypeShape.const_spine (H : RecursiveTypeShape c (mkApps (.const name ls) args)) :
    name = c ∧ args = [] := by
  generalize he : mkApps (.const name ls) args = e at H
  have hh := congrArg VExpr.getAppFnArgs he
  rw [VExpr.getAppFnArgs_mkApps_const] at hh
  cases H with
  | const => exact ⟨(VExpr.const.inj (congrArg Prod.fst hh)).1, congrArg Prod.snd hh⟩
  | forallE => cases congrArg Prod.fst hh

variable [Params]

/-- Sort typing rules out the proof and function-eta branches of normal
comparison, leaving its left-domain marker unchanged. -/
theorem RecursiveTypeShape.normal (H : NormalEqN mode n Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.IsType univs Γ e)
    (hs : RecursiveTypeShape c e) : RecursiveTypeShape c out := by
  induction H with
  | refl => exact hs
  | constDF => cases hs; exact .const
  | forallEDF hA _ _ _ ihA _ =>
    cases hs with
    | forallE hs => exact .forallE (ihA hΓ ⟨_, hA.hasType.2⟩ hs)
  | etaR hf _ _ | etaBoth hf _ _ _ =>
    obtain ⟨_, ht⟩ := ht
    exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  | proofIrrel hP he _ =>
    obtain ⟨_, ht⟩ := ht
    exact (not_isProof_of_sort hΓ ht ⟨_, he, hP⟩).elim
  | sortDF | appDF | projDF | lamDF | etaL => cases hs

/-- Every installed constant-head unfolding of the marked name retains its
marker. This is a syntactic rule invariant, not a conversion assumption. -/
def RecursiveTypeRules (c : Name) : Prop :=
  ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check} {ls captures},
    Pat (.const c) r → RecursiveTypeShape c (r.1.apply ls captures)

/-- Core parallel reduction preserves the left-domain marker when its
constant-head equations do. -/
theorem RecursiveTypeShape.parRed (hr : RecursiveTypeRules c)
    (R : ParRed Γ e out) (hs : RecursiveTypeShape c e) : RecursiveTypeShape c out := by
  induction R with
  | const => cases hs; exact .const
  | forallE _ _ ih _ => cases hs with | forallE hs => exact .forallE (ih hs)
  | extra hp hm _ _ _ =>
    obtain ⟨sp, rfl⟩ := pat_simple hp
    cases hs with
    | const =>
      cases sp with
      | defn => cases hm; exact hr hp
      | iota => cases hm
    | forallE => cases sp <;> cases hm
  | bvar | sort | app | proj | lam | beta => cases hs

/-- An ordinary recursive definition cannot also be a generated singleton or
quotient prefix. Sort typing excludes both eta expansions at the marked spine. -/
theorem RecursiveTypeShape.fullStep (hr : RecursiveTypeRules c)
    (hrec : recursorData c = none) (hquot : c ≠ ``Quot.lift)
    (R : FullStep Γ e out) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.IsType univs Γ e) (hs : RecursiveTypeShape c e) : RecursiveTypeShape c out := by
  induction R with
  | core R => exact hs.parRed hr R
  | delta R =>
    obtain ⟨rfl, rfl⟩ := hs.const_spine
    cases R with
    | intro hl => rw [hrec] at hl; cases hl
  | quotDelta R =>
    exact (hquot hs.const_spine.1.symm).elim
  | structEta hi _ _ hm _ =>
    obtain ⟨_, ht⟩ := ht
    exact (HasType.sortTele_not_rigid hΓ (henv.projectionRigid hi)
      (as := []) (doms := []) ht hm).elim
  | funEta hf =>
    obtain ⟨_, ht⟩ := ht
    exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  | forallE _ _ ih _ =>
    cases hs with
    | forallE hs =>
      obtain ⟨_, ht⟩ := ht
      exact .forallE (ih hΓ (HasType.forallE_inv henv.ordered ht).1 hs)
  | projIota | app | proj | lam => cases hs

/-- Every finite full path from a marked sort-typed expression retains its
marker, including reductions under arbitrary Pi bodies. -/
theorem RecursiveTypeShape.fullReduction (hr : RecursiveTypeRules c)
    (hrec : recursorData c = none) (hquot : c ≠ ``Quot.lift)
    (R : FullReduction Γ e out) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.IsType univs Γ e) (hs : RecursiveTypeShape c e) : RecursiveTypeShape c out := by
  obtain ⟨u, ht⟩ := ht
  induction R with
  | rfl => exact hs
  | tail R S ih => exact ih.fullStep hr hrec hquot S hΓ ⟨_, FullReduction.hasType hΓ R ht⟩

omit [Params] in
/-- Distinct recursive markers cannot be definitionally equal in the full
canonical-Eq calculus when their installed rules preserve those markers. -/
theorem recursive_type_separation {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hc : @RecursiveTypeRules (henv.params U) c) (hd : @RecursiveTypeRules (henv.params U) d)
    (hrc : env.recursorRegistry c = none) (hrd : env.recursorRegistry d = none)
    (hqc : c ≠ ``Quot.lift) (hqd : d ≠ ``Quot.lift) (hne : c ≠ d)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ (.const c ls) (.sort u)) :
    ¬ env.IsDefEqU U Γ (.const c ls) (.const d ls') := by
  letI := henv.params U
  intro H
  have H := H.of_l henv hΓ ht
  obtain ⟨left, right, Rl, Rr, n, HN⟩ := henv.church_rosser heq hΓ H
  have hl := RecursiveTypeShape.fullReduction hc hrc hqc Rl hΓ ⟨_, ht⟩ .const
  have hr := RecursiveTypeShape.fullReduction hd hrd hqd Rr hΓ ⟨_, H.hasType.2⟩ .const
  have hlr := hl.normal HN hΓ ⟨_, FullReduction.hasType hΓ Rl ht⟩
  exact hne (hlr.unique hr)

omit [Params] in
/-- An actually installed `D := D → (Prop → Prop)` declaration satisfies the
finite marker invariant and cannot also have singleton-prefix computation. -/
theorem recursive_definition_rules {env : VEnv} (henv : env.WF)
    (H : DefinitionRegistered env (GuardedEta.declaration c)) :
    @RecursiveTypeRules (henv.params U) c ∧ env.recursorRegistry c = none := by
  letI := henv.params U
  have hp : ConcretePattern env (.const c)
      (.fixed (GuardedEta.declaration c).value (H.closed henv), .true) :=
    .inl (.intro (henv.definitionRegistry_of_defeq H) (H.closed henv))
  refine ⟨?_, (ConcretePattern.const_not_unfolding henv hp).1⟩
  intro r ls captures hp'
  have he := (ConcretePattern.uniq henv hp' hp .refl (Pattern.inter_self _)).2.2
  cases he
  change RecursiveTypeShape c ((GuardedEta.domainValue c).instL ls)
  exact .forallE .const

omit [Params] in
/-- Two distinct declarations of the same recursive equation remain distinct
types. This excludes identification based only on their infinite unfoldings. -/
theorem distinct_recursive_definitions {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hc : DefinitionRegistered env (GuardedEta.declaration c))
    (hd : DefinitionRegistered env (GuardedEta.declaration d))
    (hqc : c ≠ ``Quot.lift) (hqd : d ≠ ``Quot.lift) (hne : c ≠ d)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ¬ env.IsDefEqU U Γ (GuardedEta.domain c) (GuardedEta.domain d) := by
  obtain ⟨hrc, hnc⟩ := recursive_definition_rules (U := U) henv hc
  obtain ⟨hrd, hnd⟩ := recursive_definition_rules (U := U) henv hd
  exact recursive_type_separation henv heq hrc hrd hnc hnd hqc hqd hne hΓ
    (GuardedEta.domain_typed hc.1 U Γ)

omit [Params] in
/-- Installing two fresh copies of the recursive declaration gives an actual
well-formed canonical-Eq environment in which their types are not convertible. -/
theorem canonical_distinct_recursive_types (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfc : base.constants c = none) (hfd : base.constants d = none)
    (hqc : c ≠ ``Quot.lift) (hqd : d ≠ ``Quot.lift) (hne : c ≠ d) :
    let env := GuardedEta.extended (GuardedEta.extended base c) d
    env.WF ∧ env.HasCanonicalEq ∧
      ∀ {U Γ}, OnCtx Γ (env.IsType U) →
        ¬ env.IsDefEqU U Γ (GuardedEta.domain c) (GuardedEta.domain d) := by
  have hwc := GuardedEta.extended_wf hbase hfc
  have hfd' : (GuardedEta.extended base c).constants d = none := by
    simpa only [GuardedEta.extended, VEnv.addDefEq, GuardedEta.stub, if_neg hne] using hfd
  have hstep := GuardedEta.declaration_wf hfd'
  have hw := GuardedEta.extended_wf hwc hfd'
  have hEq := GuardedEta.extended_canonicalEq
    (GuardedEta.extended_canonicalEq heq hfc) hfd'
  have hc : DefinitionRegistered (GuardedEta.extended base c) (GuardedEta.declaration c) :=
    ⟨by simp [GuardedEta.extended, GuardedEta.stub, GuardedEta.declaration, VEnv.addDefEq], .inl rfl⟩
  have hd : DefinitionRegistered (GuardedEta.extended (GuardedEta.extended base c) d)
      (GuardedEta.declaration d) :=
    ⟨by simp [GuardedEta.extended, GuardedEta.stub, GuardedEta.declaration, VEnv.addDefEq], .inl rfl⟩
  exact ⟨hw, hEq, fun hΓ => distinct_recursive_definitions hw hEq
    (hc.mono hstep.le) hd hqc hqd hne hΓ⟩

end Lean4Lean.VEnv.Strengthening
