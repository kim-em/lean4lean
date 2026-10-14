import Lean4Lean.Theory.Typing.Strengthening.PrefixStep
import Lean4Lean.Theory.Typing.Strengthening.PrefixHeadPreservation

/-! # Finite projection computation exposes its first field selection

Every finite actual prefix path from a projection either retains that projection
and computes only its major, or first computes the major to a saturated registered
constructor and then computes the selected field. The major may be arbitrary.
The decomposition does not assume normalization, confluence or source typing.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- A single projection contraction either occurs in its major or selects one
field from an already displayed saturated constructor. -/
private theorem pattern_projection_step
    (R : PatternStep D (.proj family index major) out) :
    (∃ major', PatternCompute D major major' ∧ out = .proj family index major') ∨
    ∃ info levels args field, env.projections family info ∧
      major = mkApps (.const info.ctorName levels) args ∧
      args.length = info.nparams + info.numFields ∧
      args[info.nparams + index]? = some field ∧ out = field := by
  generalize hsrc : VExpr.proj family index major = source at R
  cases R with
  | pattern hp _ hm _ =>
    obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
    rw [← hsrc] at hh
    cases hh
  | proj R => cases hsrc; exact .inl ⟨_, R.toCompute, rfl⟩
  | projIota hi hl hg =>
    obtain ⟨rfl, rfl, he⟩ := VExpr.proj.inj hsrc
    exact .inr ⟨_, _, _, _, hi, he, hl, hg, rfl⟩
  | delta | beta | appL | appR | lamL | lamR | forallL | forallR => cases hsrc

private theorem prefix_projection_step
    (R : PrefixStep D Γ (.proj family index major) out) :
    (∃ major', PrefixCompute D Γ major major' ∧ out = .proj family index major') ∨
    ∃ info levels args field, env.projections family info ∧
      major = mkApps (.const info.ctorName levels) args ∧
      args.length = info.nparams + info.numFields ∧
      args[info.nparams + index]? = some field ∧ out = field := by
  generalize hsrc : VExpr.proj family index major = source at R
  cases R with
  | base R =>
    rcases pattern_projection_step (hsrc ▸ R) with ⟨major', RM, he⟩ | H
    · exact .inl ⟨major', .base RM, he⟩
    · exact .inr H
  | singleton | quotient =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | proj R => cases hsrc; exact .inl ⟨_, R.toCompute, rfl⟩
  | appL | appR | lamL | lamR | forallL | forallR => cases hsrc

/-- Arbitrary finite projection computation records a major path to the first
selected constructor and the entire subsequent field path, or retains the
projection without selecting any field. -/
theorem PrefixCompute.projection_trace
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PrefixCompute D Γ (.proj family index major) out) :
    (∃ major', PrefixCompute D Γ major major' ∧ out = .proj family index major') ∨
    ∃ info levels args field, env.projections family info ∧
      PrefixCompute D Γ major (mkApps (.const info.ctorName levels) args) ∧
      args.length = info.nparams + info.numFields ∧
      args[info.nparams + index]? = some field ∧ PrefixCompute D Γ field out := by
  apply prefix_induct_steps hcon R (P := fun out =>
    (∃ major', PrefixCompute D Γ major major' ∧ out = .proj family index major') ∨
    ∃ info levels args field, env.projections family info ∧
      PrefixCompute D Γ major (mkApps (.const info.ctorName levels) args) ∧
      args.length = info.nparams + info.numFields ∧
      args[info.nparams + index]? = some field ∧ PrefixCompute D Γ field out)
    (.inl ⟨major, .refl, rfl⟩)
  intro x y R H
  rcases H with ⟨major', RM, rfl⟩ | ⟨info, levels, args, field, hi, RM, hl, hg, RF⟩
  · rcases prefix_projection_step R with ⟨major'', RM', he⟩ |
      ⟨info, levels, args, field, hi, he, hl, hg, rfl⟩
    · exact .inl ⟨major'', RM.trans RM', he⟩
    · exact .inr ⟨info, levels, args, _, hi, he ▸ RM, hl, hg, .refl⟩
  · exact .inr ⟨info, levels, args, field, hi, RM, hl, hg, RF.trans R.toCompute⟩

/-- If the major is computationally fixed and is not a displayed constructor,
its projection is fixed as well. This includes arbitrary neutral syntax, not
only variables. -/
theorem PrefixCompute.projection_fixed
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hfix : ∀ out, PrefixCompute D Γ major out → out = major)
    (hn : ∀ info levels args, env.projections family info →
      major ≠ mkApps (.const info.ctorName levels) args)
    (R : PrefixCompute D Γ (.proj family index major) out) :
    out = .proj family index major := by
  rcases R.projection_trace hcon with ⟨major', RM, he⟩ |
    ⟨info, levels, args, field, hi, RM, _, _, _⟩
  · exact he.trans (congrArg (VExpr.proj family index) (hfix _ RM))
  · exact (hn info levels args hi (hfix _ RM).symm).elim

end Lean4Lean.VEnv.Strengthening.PureObservation
