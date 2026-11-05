import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePostInstantiationTypes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryLocalSquare

/-! # Historical type-valued cuts from the instantiation joining premise

The argument and the generic body may both compute, without native argument
recovery. Arbitrary component rounds are retained by the existing historical
invariant. HJ supplies joining of their contractions, including bodies that
become types only after substitution. Full cut-development joining remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Independent computation of an argument and a generic body joins the
original type-valued contractum. First compute the argument through the original
body, then use HJ at its typed realized image. This composes a forward path with
one join, rather than composing two arbitrary joins. No native image is needed. -/
theorem TypeInstantiationJoin.body_argument_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hbi : env.HasType univs Γ (b.inst x) (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) body)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (body.inst image) shared := by
  obtain ⟨y, Hxy, Ey⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA.1 hx rfl rfl RX
  have hby := (IsDefEq.trans_l henv hΓA.1 hbi (IsDefEq.instDF henv.ordered hΓA.1 hb Hxy)).hasType.2
  have RI := proofErase_static_structure_compute_inst_argument heq hs hΓA hb hx RX
  have EI := proofErase_instN hΓA Hxy.hasType.2 Ctx.InstN.zero hb
  rw [Ey] at EI
  rw [← EI] at RI
  obtain ⟨shared, RL, RR⟩ := HJ.instN_of_instantiated_type heq hs Hxy.hasType.2
    Ctx.InstN.zero hΓA hb hby RB
  exact ⟨shared, RI.trans RL, by simpa only [Ey] using RR⟩

/-- Historical component paths join contraction without the initial native
argument premise. The original contractum must be type-valued; its generic
body may have an arbitrary dependent type. The result is joining, not exact
forward transport to the final raw contractum. -/
theorem CutComponentHistory.type_contract_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hbi : env.HasType univs Γ (b.inst x) (.sort v)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (s.2.1.inst s.2.2) shared := by
  obtain ⟨⟨_, HA, _, _⟩, ⟨_, HB, _, RB⟩, ⟨_, HX, _, RX⟩⟩ := H
  exact HJ.body_argument_join heq hs ⟨hΓ, u, HA.hasType.1⟩ HB.hasType.1 HX.hasType.1 hbi RB RX

/-- A historical type-valued cut retains a sort assignment at its current
raw source, despite changes to its annotation, body and argument. This ordinary
replay fact excludes function and structure eta at the whole cut. -/
theorem CutComponentHistory.type_source
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort v)) :
    ControlTyping (proofEraseCtx Γ) s.redex (.sort v) := by
  obtain ⟨⟨C, HAC, EC, _⟩, ⟨d, Hbd, Ed, _⟩, ⟨y, Hxy, Ey, _⟩⟩ := H
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hdC := Hbd.hasType.2.defeqDFC henv HC
  have EdC : proofErase (C :: Γ) d = s.2.1 :=
    (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
  have HE := IsDefEq.appDF (IsDefEq.lamDF HAC Hbd) Hxy
  have hcurrent := (IsDefEq.trans_l henv hΓ ht HE).hasType.2
  have hn := not_isProof_of_sort hΓ hcurrent
  have hnf := not_isProof_fn hΓ (HasType.lam HAC.hasType.2 hdC) (HAC.defeq Hxy.hasType.2) hn
  refine ⟨Γ, .app (.lam C d) y, hΓ, rfl, hcurrent, ?_⟩
  rw [show proofErase Γ (.app (.lam C d) y) = .app _ _ from if_neg hn,
    show proofErase Γ (.lam C d) = .lam _ _ from if_neg hnf, EC, EdC, Ey]
  rfl

/-- A primitive at the whole historical type cut is a constant or identity
wrapper: sort typing excludes function and structure eta. Both wrappers beta
contract to the historical contractum, which joins by HJ without native recovery. -/
theorem CutComponentHistory.type_primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort v))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) s.redex expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) expanded shared := by
  have HC := H.type_source hΓ ht
  obtain ⟨_, HB, _, _⟩ := H.2.1
  obtain ⟨_, HX, _, _⟩ := H.2.2
  have hbi := (IsDefEq.trans_l henv hΓ ht (IsDefEq.beta HB.hasType.1 HX.hasType.1)).hasType.2
  obtain ⟨shared, RL, RR⟩ := H.type_contract_join heq hs HJ hΓ hbi
  rcases static_structure_beta_redex_primitive RP with RC | RI | RE | RS
  · cases RC
    exact ⟨shared, RL, (ScopedCompute.beta ((constantExpansion_beta _).trans .beta)).trans RR⟩
  · cases RI with
    | intro _RN =>
      rename_i annotation
      have RB : BetaRed (.app (.lam annotation (.bvar 0)) s.redex) s.redex := by
        simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
          ProofShape.liftN_zero] using (BetaRed.beta (A := annotation) (b := .bvar 0) (a := s.redex))
      exact ⟨shared, RL, (ScopedCompute.beta (RB.trans .beta)).trans RR⟩
  · exact (HC.no_eta_sort (erased_static_structure_eta_expansion_union_descent heq hs) RE).elim
  · exact (HC.no_masked_structure (erased_static_structure_eta_expansion_union_descent heq hs) RS).elim

/-- Every single-occurrence competitor at a historical type-valued cut joins
its original contraction under HJ. All component histories and function-root
expansions are included. An unrestricted continuation after this final step is
not covered: local squares alone do not imply nonterminating confluence. -/
theorem CutComponentHistory.type_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort v))
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.redex out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  obtain ⟨_, HB, _, _⟩ := H.2.1
  obtain ⟨_, HX, _, _⟩ := H.2.2
  have hbi := (IsDefEq.trans_l henv hΓ ht (IsDefEq.beta HB.hasType.1 HX.hasType.1)).hasType.2
  have hn := not_isProof_of_sort hΓ ht
  change ScopedStep _ _ (.app (.lam s.1 s.2.1) s.2.2) out at R
  cases R with
  | primitive RP => exact H.type_primitive_square heq hs HJ hΓ ht RP
  | beta => exact H.type_contract_join heq hs HJ hΓ hbi
  | appL RF =>
    cases RF with
    | primitive RP =>
      obtain ⟨shared, RL, RR⟩ := H.type_contract_join heq hs HJ hΓ hbi
      obtain ⟨⟨C, HAC, EC, _⟩, ⟨d, Hbd, Ed, _⟩, ⟨y, Hxy, Ey, _⟩⟩ := H
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
      have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
      have hdC := Hbd.hasType.2.defeqDFC henv HC
      have EdC : proofErase (C :: Γ) d = s.2.1 :=
        (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
      have HE := IsDefEq.appDF (IsDefEq.lamDF HAC Hbd) Hxy
      have hnr : ¬ IsProof Γ (.app (.lam C d) y) := fun hp => hn ((isProof_congr hΓ HE).2 hp)
      have hnf := not_isProof_fn hΓ (HasType.lam HAC.hasType.2 hdC) (HAC.defeq Hxy.hasType.2) hnr
      have EF : proofErase Γ (.lam C d) = .lam s.1 s.2.1 := by
        rw [show proofErase Γ (.lam C d) = .lam _ _ from if_neg hnf, EC, EdC]
      have RB := literal_lambda_primitive_application_beta heq hs hΓ HAC.hasType.2 hdC hnf (EF ▸ RP) s.2.2
      rw [EdC] at RB
      exact ⟨shared, RL, (ScopedCompute.beta RB).trans RR⟩
    | lamDomain RA =>
      rename_i C'
      have HH : CutComponentHistory D Γ A b x u B (C', s.2.1, s.2.2) :=
        H.advance heq hs hΓ ⟨RA.compute, .refl, .refl⟩
      obtain ⟨shared, RL, RR⟩ := HH.type_contract_join heq hs HJ hΓ hbi
      exact ⟨shared, RL, (ScopedCompute.beta .beta).trans RR⟩
    | lamBody RB =>
      rename_i d'
      have HH : CutComponentHistory D Γ A b x u B (s.1, d', s.2.2) :=
        H.advance heq hs hΓ ⟨.refl, RB.compute, .refl⟩
      obtain ⟨shared, RL, RR⟩ := HH.type_contract_join heq hs HJ hΓ hbi
      exact ⟨shared, RL, (ScopedCompute.beta .beta).trans RR⟩
  | appR RX =>
    rename_i y'
    have HH : CutComponentHistory D Γ A b x u B (s.1, s.2.1, y') :=
      H.advance heq hs hΓ ⟨.refl, .refl, RX.compute⟩
    obtain ⟨shared, RL, RR⟩ := HH.type_contract_join heq hs HJ hΓ hbi
    exact ⟨shared, RL, (ScopedCompute.beta .beta).trans RR⟩

/-- Any finite number of interleaved component rounds followed by one
single-occurrence step joins the original type-valued contraction under HJ.
Domains may change repeatedly and argument recovery may be absent throughout.
This is a historical local square, not a strip theorem for arbitrary whole-cut
computations or a proof that HJ suffices for strengthening. -/
theorem TypeInstantiationJoin.type_cut_development_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort v))
    (RC : ReflTransGen (CutComponentRound D (proofEraseCtx Γ))
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) s)
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.redex out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared :=
  ((CutComponentHistory.refl hA hb hx).rounds heq hs hΓ RC).type_step_square heq hs HJ hΓ ht R

end Lean4Lean.VEnv.Strengthening
