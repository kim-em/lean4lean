import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual

/-! # Future record checking with dependent field carriers

Carrier parameters and both majors may beta-reduce independently. Dependent
field recipes track the new parameters and left major, including all preceding
projections. Their exact substitution theorem retains the same recursive
certificates after interpreted substitution; no global carrier-conversion law
is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
variable [Params]

/-- Future common comparisons of every retained projection supply a future
record guard. Carrier beta may change every parameter independently; field
proof status and universe admissibility are fixed by the registration. -/
theorem BetaStableCarrier.record_fields
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ (.proj family i a) (.proj family i b)) :
    BetaStableCarrier Step Δ (mkApps (.const family ls) ps) a b := by
  constructor
  · intro A' p q RC RP RQ
    obtain ⟨ps', rfl, HP⟩ := RC.const_spine
    apply JointCheck.carrierIntro hi hx (HP.length_eq.symm.trans hp) hadm
    intro i hj hn
    exact (H i hj hn).1 (.proj RP) (.proj RQ)
  · intro Δ' τ A' p q W RC RP RQ
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RC
    obtain ⟨ps', rfl, HP⟩ := RC.const_spine
    apply JointCheck.carrierIntro hi hx (by have := HP.length_eq; simp only [List.length_map] at this; omega) hadm
    intro i hj hn
    exact (H i hj hn).2 W (.proj RP) (.proj RQ)

/-- Recursive future field certificates combine at the full dependent record.
After substitution, the closed telescope identifies the exact instantiated
field recipe. Subsequent parameter and major beta paths reduce that recipe,
so its stored carrier certificate applies at every new dependent field type. -/
theorem BetaStableCarrier.record_nested
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result)
    (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      BetaStableCarrier Step Δ
        (projectionType family info doms i (by have := HT.numFields; omega) ps a)
        (.proj family i a) (.proj family i b)) :
    BetaStableCarrier Step Δ (mkApps (.const family ls) ps) a b := by
  refine ⟨JointCarrierTypeBetaResidual.record_nested hi hx hp hadm HT (fun i hj hn => (H i hj hn).1), ?_⟩
  intro Δ' τ A' p q W RC RP RQ
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at RC
  apply JointCarrierTypeBetaResidual.record_nested hi hx (by simpa only [List.length_map] using hp) hadm HT ?_ RC RP RQ
  intro i hj hn
  have HC := (H i hj hn).subst W
  simp only [projectionType_subst (args := ps) HT _ (by omega), ProofShape.subst] at HC
  exact fun {_ _ _} R S T => HC.1 R S T

/-- Projection of future inferred major comparisons gives future comparisons
of the selected fields. Beta changes the majors only; interpreted substitution
is retained by the major certificate. Primitive projection reduction is not
part of the future beta path quantified here. -/
theorem BetaStableFamily.proj
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ false) Δ a b) :
    BetaStableFamily (fun Δ => JointCompare Step Δ mode) Δ (.proj family i a) (.proj family i b) := by
  constructor
  · intro p q RP RQ
    obtain ⟨p', rfl, RA⟩ := ProofShape.beta_proj_inv RP
    obtain ⟨q', rfl, RB⟩ := ProofShape.beta_proj_inv RQ
    exact .proj (H.1 RA RB)
  · intro Δ' τ p q W RP RQ
    obtain ⟨p', rfl, RA⟩ := ProofShape.beta_proj_inv RP
    obtain ⟨q', rfl, RB⟩ := ProofShape.beta_proj_inv RQ
    exact .proj (H.2 W RA RB)

end Lean4Lean.VEnv.Strengthening
