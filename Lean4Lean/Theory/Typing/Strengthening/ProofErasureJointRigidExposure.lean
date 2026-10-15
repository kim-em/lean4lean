import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreConfluence

/-! # Rigid family exposure from joint comparison

Inferred comparison against a rigid constant spine supplies a computation of
the other endpoint to that same family, with the same arity. This includes
carrier-aware applications. Empty-structure carrier guards can therefore
transfer along type comparison without a literal common reduct of the types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private const_spine_app from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
variable [Params]

/-- A generated singleton code heads an actual stored equation, so it cannot
have a rigid head. This uses the closed code certificate, not its family guard. -/
theorem SingletonPrefixCode.Valid.not_rigid (V : SingletonPrefixCode.Valid C) :
    ¬ env.Rigid C.data.name := by
  intro hrig
  obtain ⟨r, ru, hc, hof, hp⟩ := V.registered.singletonEquation V.equation_eq
  obtain ⟨index, howner, hgen⟩ := RecursorData.singletonEquation_eq V.equation_eq
  have hhead := V.registered.equation_head howner hgen
  have hname := hof.2.1
  rw [lamBody_eq_stripLams, VExpr.headConst?_eq_some] at hname
  obtain ⟨us, hname⟩ := hname
  rw [VExpr.getAppFn_eq_fst, hhead] at hname
  have hrname := (VExpr.const.inj hname).1.symm
  exact hrig.pats _ _ hp (by rw [SimplePattern.iota_headConst, hrname])

/-- No joint stage introduces a primitive at a rigid head excluded by the core.
Both generated singleton rules and the canonical Eq prefix are ruled out by
stored-rule provenance, independently of their recursive comparison guards. -/
theorem erased_joint_stage_no_rigid (heq : env.HasCanonicalEq)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∀ stage {Δ a b}, ErasedJointStage D stage Δ a b → a.constHead = some c → False := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_no_rigid hc hD
  | succ stage ih =>
    intro Δ a b H hh
    rcases H with H | H | H
    · exact ih H hh
    · cases H.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact V.not_rigid (hn ▸ hc)
    · cases H with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)

/-- Rigid-head exclusion persists in the entire joint union. -/
theorem erased_joint_union_no_rigid (heq : env.HasCanonicalEq)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : ErasedJointUnion D Δ a b) (hh : a.constHead = some c) : False := by
  obtain ⟨stage, H⟩ := H
  exact erased_joint_stage_no_rigid heq hc hD stage H hh

namespace ProofShape

omit [Params] in
private theorem const_spine_const (E : mkApps (.const c ls) args = .const c' ls') :
    c = c' ∧ ls = ls' ∧ args = [] := by
  cases args using List.snoc_induction with
  | nil => obtain ⟨rfl, rfl⟩ := ProofShape.const.inj E; exact ⟨rfl, rfl, rfl⟩
  | snoc args a => rw [mkApps_snoc] at E; cases E

private theorem const_exposure_pair
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const c ls) args) out)
    (H : JointCheck Step Δ kind a b) (hm : kind = .compare false) :
    (∀ ls args, a = mkApps (.const c ls) args →
      ∃ ls' args', ScopedCompute Step Δ b (mkApps (.const c ls') args') ∧ args'.length = args.length) ∧
    (∀ ls args, b = mkApps (.const c ls) args →
      ∃ ls' args', ScopedCompute Step Δ a (mkApps (.const c ls') args') ∧ args'.length = args.length) := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl => exact ⟨fun ls args E => ⟨ls, args, E ▸ .refl, rfl⟩,
        fun ls args E => ⟨ls, args, E ▸ .refl, rfl⟩⟩
    | sort =>
      constructor <;> intro ls args E <;>
        have HE := congrArg constHead E <;>
        simp only [constHead_mkApps, constHead] at HE <;> cases HE
    | const =>
      constructor
      · intro ls args E
        obtain ⟨rfl, rfl, rfl⟩ := const_spine_const E.symm
        exact ⟨_, [], .refl, rfl⟩
      · intro ls args E
        obtain ⟨rfl, rfl, rfl⟩ := const_spine_const E.symm
        exact ⟨_, [], .refl, rfl⟩
  | @app Δ f g x y mode HF HX ihf ihx =>
    have IH := ihf rfl
    constructor
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, hlen⟩ := IH.1 ls args₀ Ef
      refine ⟨ls', args' ++ [y], ?_, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, hlen⟩ := IH.2 ls args₀ Ef
      refine ⟨ls', args' ++ [x], ?_, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  | @appCarrier Δ f A B g x y mode R HF HX ihf ihx =>
    have IH := ihf rfl
    constructor
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, hlen⟩ := IH.1 ls args₀ Ef
      refine ⟨ls', args' ++ [y], ?_, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, hlen⟩ := IH.2 ls args₀ Ef
      refine ⟨ls', args' ++ [x], ?_, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro ls args E <;>
      have HE := congrArg constHead E <;>
      simp only [constHead_mkApps, constHead] at HE <;> cases HE
  | compute Ra Rb HC ih =>
    have IH := ih hm
    constructor
    · intro ls args E
      obtain ⟨args₁, E₁, H₁⟩ := (E ▸ Ra).const_spine hn
      obtain ⟨ls', args', R, hlen⟩ := IH.1 ls args₁ E₁
      exact ⟨ls', args', Rb.trans R, hlen.trans H₁.length_eq.symm⟩
    · intro ls args E
      obtain ⟨args₁, E₁, H₁⟩ := (E ▸ Rb).const_spine hn
      obtain ⟨ls', args', R, hlen⟩ := IH.2 ls args₁ E₁
      exact ⟨ls', args', Ra.trans R, hlen.trans H₁.length_eq.symm⟩
  | symm H ih => exact (ih hm).symm
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Inferred comparison against a primitive-inert constant spine exposes the
same head and arity on the other side. This requires no typing, confluence,
substitution law, or comparison of the actual parameter syntax. -/
theorem JointCompare.const_spine_exposure
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const c ls) args) out)
    (H : JointCompare Step Δ false (mkApps (.const c ls) args) b) :
    ∃ ls' args', ScopedCompute Step Δ b (mkApps (.const c ls') args') ∧ args'.length = args.length :=
  (const_exposure_pair hn H rfl).1 ls args rfl

/-- Type comparison with a displayed empty registered structure supplies a
carrier guard at the other type for any endpoints. The family exposure path
replaces a literal join of the parameterized types. Sound use still supplies
the endpoint typings at the target carrier. -/
theorem JointCompare.unit_carrier_target
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (H : JointCompare Step Δ false (mkApps (.const family ls) ps) T) :
    JointCarrierGuard Step Δ T a b := by
  obtain ⟨ls', ps', R, hlen⟩ := H.const_spine_exposure hn
  exact .carrierCompute R (.carrierSubsingleton (.unit hi hx hf (hlen.trans hp)))

end ProofShape
end Lean4Lean.VEnv.Strengthening
