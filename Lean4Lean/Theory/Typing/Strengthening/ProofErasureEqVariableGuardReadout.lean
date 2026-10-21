import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFreshVariableReadout

/-! # Reading equality endpoints at a variable carrier

Native recovery at an inert variable carrier forces carrier checking back to
common comparison. This handles the fully open canonical Eq.rec guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_recovery from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private bvar_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFreshVariableReadout
variable [Params]

private theorem eq_bvar_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.app (.const ``Eq [u]) (.bvar i)) T) :
    T = .forallE (.bvar i) (.forallE (.bvar (i+1)) (.sort .zero)) := by
  generalize E : ProofShape.app (.const ``Eq [u]) (.bvar i) = e at R
  induction R with
  | app R =>
    cases E
    cases eq_recovery heq hhead R
    simp [ProofShape.inst, ProofShape.liftN, liftVar, Nat.add_comm]
  | convert _ H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
        ⟨fun _ H => hhead H, trivial⟩⟩⟩
  | bvar | sort | const | lam | forallE | proj => cases E

private theorem eq_bvar_prefix_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.app (.app (.const ``Eq [u]) (.bvar i)) z) T) :
    T = .forallE (.bvar i) (.sort .zero) := by
  generalize E : ProofShape.app (.app (.const ``Eq [u]) (.bvar i)) z = e at R
  induction R with
  | app R =>
    cases E
    cases eq_bvar_recovery heq hhead R
    simp [ProofShape.inst]
  | convert _ H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨fun _ H => hhead H, trivial⟩⟩
  | bvar | sort | const | lam | forallE | proj => cases E

private def eqBvar (u : VLevel) (i : Nat) (z a : ProofShape) : ProofShape :=
  .app (.app (.app (.const ``Eq [u]) (.bvar i)) z) a

omit [Params] in
private theorem eq_bvar_compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (R : ScopedCompute Step Δ (eqBvar u i z a) out) :
    ∃ z' a', out = eqBvar u i z' a' ∧
      ScopedCompute Step Δ z z' ∧ ScopedCompute Step Δ a a' := by
  change ScopedCompute Step Δ (mkApps (.const ``Eq [u]) [.bvar i, z, a]) out at R
  obtain ⟨args, E, H⟩ := R.const_spine hn
  cases H with
  | cons Hv H => cases H with
    | cons Hz H => cases H with
      | cons Ha H =>
        cases H
        rw [bvar_fixed hhead Hv] at E
        exact ⟨_, _, E, Hz, Ha⟩

private theorem eq_bvar_decode_raw
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (H : JointCheck Step Δ kind sa sb) (hm : kind = .compare false)
    (Ea : sa = eqBvar u i z a) (Eb : sb = eqBvar u' i' z' b) :
    JointCompare Step Δ true a b := by
  induction H generalizing u i z a u' i' z' b with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have EE := Ea.symm.trans Eb
      exact (ProofShape.app.inj EE).2 ▸ JointCheck.leaf ScopedLeaf.refl
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact HX
  | appCarrier R HF HX =>
    cases Ea
    cases Eb
    cases eq_bvar_prefix_recovery heq hhead R
    exact JointCarrierGuard.bvar_spine_checked (args := []) hhead HX
  | compute Ra Rb HC ih =>
    obtain ⟨za, aa, EA, Rza, Raa⟩ := eq_bvar_compute hhead hn (Ea ▸ Ra)
    obtain ⟨zb, bb, EB, Rzb, Rbb⟩ := eq_bvar_compute hhead hn (Eb ▸ Rb)
    exact .compute Raa Rbb (ih hm EA EB)
  | symm H ih => exact .symm (ih hm Eb Ea)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Inferred comparison of canonical equality propositions over bare variable carriers
compares their final arguments. Primitive computation must preserve Eq spines.
No typing, beta stability, confluence, or exact recovery of the arguments is
assumed, and the two Eq prefixes may use different endpoints, carrier indices, and universes. -/
theorem ProofShape.JointCompare.eq_bvar_decode
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (H : JointCompare Step Δ false
      (.app (.app (.app (.const ``Eq [u]) (.bvar i)) z) a)
      (.app (.app (.app (.const ``Eq [u']) (.bvar i')) z') b)) :
    JointCompare Step Δ true a b := eq_bvar_decode_raw heq hhead hn H rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
