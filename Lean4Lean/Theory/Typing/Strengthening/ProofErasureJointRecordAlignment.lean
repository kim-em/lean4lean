import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure

/-! # Record parameter alignment through neutral retained fields

If every retained field recipe stays variable-headed as parameters compute,
nested field guards supply ordinary projection comparisons. Those comparisons
support the same registered record at new parameters. The criterion refers to
the actual dependent projection recipes, not merely to the record's outer head.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private const_spine_const from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure

private theorem const_spine_inj
    (E : mkApps (.const c ls) ps = mkApps (.const c' ls') ps') :
    c = c' ∧ ls = ls' ∧ ps = ps' := by
  induction ps using List.snoc_induction generalizing ps' with
  | nil =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_const E.symm
    exact ⟨rfl, rfl, rfl⟩
  | snoc ps a ih =>
    cases ps' using List.snoc_induction with
    | nil => rw [mkApps_snoc] at E; cases E
    | snoc ps' a' =>
      rw [mkApps_snoc, mkApps_snoc] at E
      obtain ⟨Ef, rfl⟩ := ProofShape.app.inj E
      obtain ⟨rfl, rfl, rfl⟩ := ih Ef
      exact ⟨rfl, rfl, rfl⟩

variable [Params]
/-- The actual retained projection recipes remain variable-headed for every
parameter list reached by computation. Proof fields need no such condition.
The quantification over majors includes dependencies on preceding fields. -/
def NeutralRecordFields (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (family : Name) (info : VProjectionInfo)
    (ls : List VLevel) (ps : List ProofShape) : Prop :=
  ∀ {ps' doms result}, List.Forall₂ (ScopedCompute Step Δ) ps ps' →
    ProjTele env univs family info ls doms result →
    ∀ (j : Nat) (hj : info.nparams + j < doms.length) (major : ProofShape),
      j < info.numFields → ¬ StructureReplay.ProofField env univs info ls j →
      ∃ i args, projectionType family info doms j hj ps' major = mkApps (.bvar i) args

/-- Full joint carrier checking reindexes a record's parameters when its
retained field recipes remain neutral. The target parameter count is checked;
actual endpoint typings at the target carrier are needed for sound use. -/
theorem JointCarrierGuard.record_reindex_neutral_fields
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family ls) args) out)
    (hi : env.projections family info)
    (htarget : target.length = info.nparams)
    (HF : NeutralRecordFields Step Δ family info ls ps)
    (H : JointCarrierGuard Step Δ (mkApps (.const family ls) ps) a b) :
    JointCarrierGuard Step Δ (mkApps (.const family ls) target) a b := by
  change JointCheck Step Δ (.carrier (mkApps (.const family ls) ps)) a b at H
  generalize E : JointCheckKind.carrier (mkApps (.const family ls) ps) = kind at H
  induction H generalizing ps with
  | carrierChecked H => exact .carrierChecked H
  | carrierFunction =>
    have HE := congrArg ProofShape.constHead (JointCheckKind.carrier.inj E)
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | carrierSubsingleton HS =>
    cases E
    generalize EC : mkApps (.const family ls) ps = carrier at HS
    cases HS with
    | unit hi' hx hf hp =>
      obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj EC
      cases henv.ordered.projections_unique hi hi'
      exact .carrierSubsingleton (.unit hi hx hf htarget)
    | forallE =>
      have HE := congrArg ProofShape.constHead EC
      simp only [constHead_mkApps, ProofShape.constHead] at HE
      cases HE
  | carrierSymm H ih => exact .carrierSymm (ih HF E)
  | carrierCompute R H ih =>
    cases E
    obtain ⟨ps', rfl, RP⟩ := R.const_spine hinert
    apply ih (ps := ps') ?_ rfl
    intro ps'' doms result RP' HT j hj major hjf hproof
    exact HF (Lean4Lean.List.Forall₂.trans (fun _ _ _ r r' => r.trans r') RP RP')
      HT j hj major hjf hproof
  | carrierReduce RA RB H ih => exact .carrierReduce RA RB (ih HF E)
  | carrierIntro hi' hx hp hadm Hfields =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj (JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    exact .carrierIntro hi hx htarget hadm Hfields
  | carrierNested hi' hx hp hadm HT Hfields =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj (JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    apply JointCheck.carrierIntro hi hx htarget hadm
    intro j hj hn
    obtain ⟨i, args, EF⟩ := HF (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) HT j
      (by have := HT.numFields; omega) _ hj hn
    have HG : JointCarrierGuard Step _ _ _ _ := Hfields j hj hn
    rw [EF] at HG
    exact HG.bvar_spine_checked hhead
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
