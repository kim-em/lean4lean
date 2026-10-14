import Lean4Lean.Theory.Typing.Strengthening.SymmetricNeutralBoundary

/-! # Structure readout needs more than symmetric terminal eta

A registered pattern selecting a field through an identity branch gives an
actual eta, iota, beta path from a neutral recursor to a projection. With no
closed equation for that recursor, the symmetric phase cannot represent the
path. All registration, matching, guard and typing premises are explicit;
this is a conditional rule-level obstruction, not a constructed environment
or a canonical-Eq counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- An actual checked pattern with an identity-branch result contracts to the
selected projection by one core step and one beta step. -/
theorem identity_branch_readout
    (hp : Pat p r) (hm : p.Matches source levels captures)
    (hc : r.2.OK (env.IsDefEqU univs Γ) levels captures)
    (he : r.1.apply levels captures = .app (.lam A (.bvar 0)) field) :
    FullReduction Γ source field := by
  have H : FullStep Γ source (r.1.apply levels captures) :=
    .core (.extra hp hm hc (fun _ => .rfl))
  rw [he] at H
  have HB : FullStep Γ (.app (.lam A (.bvar 0)) field) field := by
    simpa only [VExpr.inst, instVar, Nat.lt_irrefl, if_false, Nat.zero_add, Nat.sub_self, if_true, VExpr.liftN_zero] using
      (FullStep.core (ParRed.beta (A := A) (e₁ := .bvar 0) (e₂ := field) .rfl .rfl))
  exact (ReflTransGen.tail .rfl H).tail HB

/-- The same readout is actual prefix computation, with the original pattern's
uniform checking certificate recovered from its concrete registration. -/
theorem identity_branch_compute
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hp : Pat p r) (hm : p.Matches source levels captures)
    (hc : r.2.OK (env.IsDefEqU univs Γ) levels captures)
    (he : r.1.apply levels captures = .app (.lam A (.bvar 0)) field) :
    PrefixCompute D Γ source field := by
  have H : PatternCompute D source (r.1.apply levels captures) :=
    .pattern hp hm (ConcretePattern.checkFromTyping henv (hcon hp) hc)
  rw [he] at H
  have HB : PatternCompute D (.app (.lam A (.bvar 0)) field) field := by
    simpa only [VExpr.inst, instVar, Nat.lt_irrefl, if_false, Nat.zero_add, Nat.sub_self, if_true, VExpr.liftN_zero] using
      (PatternCompute.of_beta (D := D) (BetaRed.beta (A := A) (b := .bvar 0) (a := field)))
  exact .base (H.trans HB)

/-- A checked structure readout after eta is an actual finite full path whose
endpoints have no symmetric phase in the original non-unfolding collection.
The neutral arguments may include lambda motives and identity branches. -/
theorem structure_readout_phase_boundary
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hv : env.HasType univs Γ (.bvar i) (mkApps (.const family ctorLevels) params))
    (hexp : env.HasType univs Γ (structExpand family info ctorLevels params (.bvar i))
      (mkApps (.const family ctorLevels) params))
    (ht : env.HasType univs Γ (.app (mkApps (.const c ls) args) (.bvar i)) (.sort u))
    (hreg : recursorData c = some data) (hz : ¬ data.sourceLevel ls ≈ .zero)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PrefixCompute D Γ a out → out = a)
    (hr : Pat p r)
    (hm : p.Matches
      (.app (mkApps (.const c ls) args) (structExpand family info ctorLevels params (.bvar i)))
      levels captures)
    (hc : r.2.OK (env.IsDefEqU univs Γ) levels captures)
    (he : r.1.apply levels captures = .app (.lam A (.bvar 0)) (.proj family index (.bvar i))) :
    FullReduction Γ (.app (mkApps (.const c ls) args) (.bvar i)) (.proj family index (.bvar i)) ∧
    ¬ PrefixEtaJoin D Γ (.app (mkApps (.const c ls) args) (.bvar i)) (.proj family index (.bvar i)) := by
  have RE : FullStep Γ (.app (mkApps (.const c ls) args) (.bvar i))
      (.app (mkApps (.const c ls) args) (structExpand family info ctorLevels params (.bvar i))) :=
    .app .rfl (.structEta hi hp hx hv hexp)
  have R := (ReflTransGen.tail .rfl RE).trans (identity_branch_readout hr hm hc he)
  refine ⟨R, ?_⟩
  rw [← mkApps_snoc]
  apply neutral_recursor_not_symmetric_phase hcon hΓ (FullReduction.hasType hΓ R ht) hreg hz hn
  · intro a ha' name levels
    rcases List.mem_append.1 ha' with h | h
    · exact ha a h name levels
    · have he : a = .bvar i := by simpa using h
      subst a
      simp [getAppFn]
  · intro a ha' out R
    rcases List.mem_append.1 ha' with h | h
    · exact hfix a h out R
    · have he : a = .bvar i := by simpa using h
      subst a
      exact R.bvar_eq

/-- Under the same explicit readout premises, symmetric phases fail to compose
through a middle typed at the very same sort as both endpoints. The missing
recursor equation, rather than an untyped intermediate, is the obstruction. -/
theorem structure_readout_symmetric_nontransitive
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hv : env.HasType univs Γ (.bvar i) (mkApps (.const family ctorLevels) params))
    (hexp : env.HasType univs Γ (structExpand family info ctorLevels params (.bvar i))
      (mkApps (.const family ctorLevels) params))
    (ht : env.HasType univs Γ (.app (mkApps (.const c ls) args) (.bvar i)) (.sort u))
    (hreg : recursorData c = some data) (hz : ¬ data.sourceLevel ls ≈ .zero)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PrefixCompute D Γ a out → out = a)
    (hr : Pat p r)
    (hm : p.Matches
      (.app (mkApps (.const c ls) args) (structExpand family info ctorLevels params (.bvar i)))
      levels captures)
    (hc : r.2.OK (env.IsDefEqU univs Γ) levels captures)
    (he : r.1.apply levels captures = .app (.lam A (.bvar 0)) (.proj family index (.bvar i))) :
    ∃ a b c, env.HasType univs Γ a (.sort u) ∧ env.HasType univs Γ b (.sort u) ∧
      env.HasType univs Γ c (.sort u) ∧ PrefixEtaJoin D Γ a b ∧
      PrefixEtaJoin D Γ b c ∧ ¬ PrefixEtaJoin D Γ a c := by
  obtain ⟨R, HN⟩ := structure_readout_phase_boundary hcon hΓ hi hp hx hv hexp ht
    hreg hz hn ha hfix hr hm hc he
  have RE : TypedEtaExpansion Γ (.app (mkApps (.const c ls) args) (.bvar i))
      (.app (mkApps (.const c ls) args) (structExpand family info ctorLevels params (.bvar i))) :=
    .app .refl (.structEta hi hp hx hv hexp)
  have RC : PrefixCompute D Γ
      (.app (mkApps (.const c ls) args) (structExpand family info ctorLevels params (.bvar i)))
      (.proj family index (.bvar i)) := identity_branch_compute hcon hr hm hc he
  have hm := (RE.simAt hΓ _ ht).hasType.2
  exact ⟨_, _, _, ht, hm, R.hasType hΓ ht, .of_eta (EtaNormal.expansion hΓ RE ht).join,
    .compute hs hΓ RC hm, HN⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
