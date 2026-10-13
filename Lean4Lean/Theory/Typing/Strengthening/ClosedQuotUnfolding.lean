import Lean4Lean.Theory.Typing.Strengthening.FieldHeadExposure
import Lean4Lean.Theory.Typing.Confluence.QuotCoverage
import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationSupply

/-! # A closed unfolding equation for Quot.lift at a Prop source

The existing checked five-argument prefix is opened at fresh variables and closed
again by eta. This yields an actual equality of the constant to a closed lambda
body, usable in every context by weakening alone. It does not assert that an
arbitrary singleton prefix, such as unaligned Eq.rec, admits the same treatment.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedQuot
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The first five binders of the specialized quotient eliminator. -/
def domains (u v : VLevel) : List VExpr :=
  ((quotLiftConst.type.instL [u,v]).takeForalls 5).getD ([], .bvar 0) |>.1

def result (u v : VLevel) : VExpr :=
  ((quotLiftConst.type.instL [u,v]).takeForalls 5).getD ([], .bvar 0) |>.2

/-- The checked five-argument unfolding under its five freshly opened binders. -/
def body (u : VLevel) : VExpr :=
  .lam (mkApps (.const ``Quot [u]) [.bvar 4, .bvar 3])
    (.app (.bvar 2) (mkApps (QuotPrefixUnfolding.propInhabitant u)
      [.bvar 5, .bvar 4, .bvar 0]))

def value (u v : VLevel) : VExpr := wrapLams (domains u v) (body u)

/-- The source constant's type is exactly this telescope and its residual type. -/
theorem type_shape : quotLiftConst.type.instL [u,v] = wrapForalls (domains u v) (result u v) := by
  simp [domains, result, quotLiftConst, instL, VLevel.inst, takeForalls, wrapForalls]

theorem domains_length : (domains u v).length = 5 := by
  simp [domains, quotLiftConst, instL, VLevel.inst, takeForalls]

/-- Opened application syntax matches the actual five-argument prefix rule. -/
theorem opened : etaOpen (domains u v).length (.const ``Quot.lift [u,v]) =
    mkApps (.const ``Quot.lift [u,v]) [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  rw [domains_length]
  simp [etaOpen, lift, liftN, liftVar, mkApps]

/-- At a Prop source, Quot.lift has a closed unfolding equation at its exact
constant type. Only the checked `atFive` rule, eta, and ordinary typing are used. -/
theorem equation (henv : env.WF) (hr : QuotRegistered env)
    (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero) :
    IsDefEq env U [] (.const ``Quot.lift [u,v]) (value u v) (quotLiftConst.type.instL [u,v]) := by
  have ht : HasType env U [] (.const ``Quot.lift [u,v])
      (wrapForalls (domains u v) (result u v)) := by
    rw [← type_shape]
    exact .const hr.lift (by simpa using And.intro hu hv) rfl
  obtain ⟨hctx, hopen⟩ := ht.etaOpen_wf henv.ordered (by trivial)
  have hsource : VExpr.WF env U ((domains u v).reverse ++ [])
      (mkApps (.const ``Quot.lift [u,v]) [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]) := by
    exact ⟨_, opened ▸ hopen⟩
  have hp := QuotPrefixUnfold.atFive henv hctx hr hu hv hz hsource
  have he : IsDefEq env U ((domains u v).reverse ++ [])
      (etaOpen (domains u v).length (.const ``Quot.lift [u,v])) (body u) (result u v) := by
    rw [opened]
    apply (hp.defeq henv hctx).of_l henv hctx
    exact opened ▸ hopen
  rw [type_shape]
  exact (ht.etaOpen_defeq henv (by trivial)).trans (he.etaOpen_wrapLams (by trivial) hctx)

/-- Closedness follows from the checked equality in the empty context. -/
theorem value_closed (henv : env.WF) (hr : QuotRegistered env)
    (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero) : (value u v).Closed :=
  (equation henv hr hu hv hz).hasType.2.closedN henv.ordered ⟨⟩

/-- Generation at the empty prefix gives exactly the closed lambda value above. -/
theorem generated_zero_rhs
    (hg : QuotPrefixUnfolding.generate [u,v] [] = some program) : program.rhs = value u v := by
  simp [QuotPrefixUnfolding.generate, quotLiftConst, quotDefEq, instL, VLevel.inst,
    InductiveSignature.RecursorData.supplyType, takeForalls, InductiveSignature.vars,
    InductiveSignature.RecursorSchema.EquationBody.extract] at hg
  cases hg
  simp [InductiveSignature.RecursorData.PrefixUnfolding.rhs, value, domains, body,
    quotLiftConst, instL, VLevel.inst, takeForalls, InductiveSignature.instantiateParams,
    VExpr.subst, wrapLams, mkApps]

/-- Every generated quotient program retains the same closed six-capture template. -/
theorem generated_template_closed
    (hg : QuotPrefixUnfolding.generate levels args = some program) :
    program.equationBody.rhs.ClosedN program.captures.length := by
  obtain ⟨_, _, _, _, heq, hb, hlen⟩ := QuotPrefixUnfolding.generate_spec hg
  rw [heq] at hb
  rw [hlen]
  have hc : ∀ b, InductiveSignature.RecursorSchema.EquationBody.extract
      quotDefEq.lhs quotDefEq.rhs quotDefEq.type = some b → b.rhs.ClosedN b.domains.length := by
    intro b h
    simp [InductiveSignature.RecursorSchema.EquationBody.extract, quotDefEq] at h
    cases h
    decide
  exact hc _ hb

/-- Supplying any admissible prefix to the zero-prefix program beta reduces to
that prefix's generated program. This is syntax, independent of occurrence checks. -/
theorem generated_prefix_beta
    (hzero : QuotPrefixUnfolding.generate levels [] = some zero)
    (hg : QuotPrefixUnfolding.generate levels args = some program) :
    BetaRed (mkApps zero.rhs args) program.rhs := by
  induction args using List.snoc_induction generalizing program with
  | nil => cases QuotPrefixUnfolding.generate_unique hzero hg; exact .refl
  | snoc args a ih =>
    have hbound := (QuotPrefixUnfolding.generate_spec hg).2.1
    obtain ⟨early, hearly⟩ := QuotPrefixUnfolding.generate_anyArity hg
      (args' := args) (by simp only [List.length_append, List.length_singleton] at hbound; omega)
    obtain ⟨A, b, he, hb⟩ := QuotPrefixUnfolding.generate_supply_one hearly hg
      (generated_template_closed hearly)
    rw [mkApps_snoc]
    apply (BetaRed.app (ih hearly) .refl).trans
    rw [he, ← hb]
    exact .beta

/-- The single closed value computes to every generated quotient prefix. -/
theorem value_prefix_beta (hg : QuotPrefixUnfolding.generate [u,v] args = some program) :
    BetaRed (mkApps (value u v) args) program.rhs := by
  obtain ⟨zero, hz⟩ := QuotPrefixUnfolding.generate_anyArity hg (args' := []) (by simp)
  have h := generated_prefix_beta hz hg
  rw [generated_zero_rhs hz] at h
  exact h

end Lean4Lean.VEnv.Strengthening.ClosedQuot
