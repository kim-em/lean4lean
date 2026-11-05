import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalStageTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalEquality
import Lean4Lean.Theory.Typing.Confluence.History

/-! # Computational certificates from a declaration's earlier stage

Adjoining the declared type formers changes no pattern rules. Strong derivations
in that well-formed intermediate environment therefore need coverage only of
the earlier registry, while their certificates live in the ambient computation
system. This supplies the intended induction interface, not earlier coverage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- The type-former extension of an installation stage is well formed, contains
the compilation's type environment, and has exactly the earlier stage's rules. -/
theorem computational_declaration_types_environment {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hstage : env₀ ∈ env.stages) (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    {base E : VEnv} (hbase : base ≤ env₀) (hE : base.addConstVals decl.typeConstants = some E) :
    ∃ envT, envT.WF ∧ envT ≤ env ∧ E ≤ envT ∧ envT.pats = env₀.pats := by
  obtain ⟨ds, H⟩ := henv.stagesH
  have hW₀ : env₀.WF := (H.stage hstage).1
  obtain ⟨envT, envC, envR, hT, -, -, -⟩ := addInduct_stages hadd
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  have hWT : envT.WF := hW₀.addConstVals (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hci
    exact hdecl.types_wf t ht) hT
  have hTle : envT ≤ env := by
    have h := addInduct_le hadd
    obtain ⟨envT', envC', envR', hT', hC', hR', hP'⟩ := addInduct_stages hadd
    rw [VInductDecl.addTypes_eq_addConstVals, hT] at hT'
    cases Option.some.inj hT'
    exact ((addCtors_le hC').trans (addProjs_le.trans ((addRecs_le hR').trans
      (addRules_le hP')))).trans hle
  have hET : E ≤ envT := addConstVals_le_target (hbase.trans (addConstVals_le hT)) hE
    (by
      intro value hvalue
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hvalue
      rw [← VInductDecl.addTypes_eq_addConstVals] at hT
      exact addTypes_find hT t ht)
  exact ⟨envT, hWT, hTle, hET, addConstVals_pats hT⟩

/-- A derivation in the declaration's type environment yields ambient chains
and computational typings when only the earlier stage's patterns are covered.
The context is arbitrary but must already be well formed in that type environment. -/
theorem stage_types_computational_typing
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hstage : env₀ ∈ env.stages) (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    (hcov : ∀ {p r}, env₀.pats p r → ComputationalPatternCoverage EnvironmentCore.definitions p r)
    {base E : VEnv} (hbase : base ≤ env₀) (hE : base.addConstVals decl.typeConstants = some E)
    (hΓ : OnCtx Γ (E.IsType univs)) (H : E.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A := by
  obtain ⟨envT, hWT, hTle, hET, hpats⟩ :=
    computational_declaration_types_environment hstage hdecl hadd hle hbase hE
  have hΓT : OnCtx Γ (envT.IsType univs) := OnCtx.mono (fun ⟨u, H⟩ => ⟨u, H.mono hET⟩) hΓ
  have hΓenv : OnCtx Γ (env.IsType univs) := OnCtx.mono (fun ⟨u, H⟩ => ⟨u, H.mono hTle⟩) hΓT
  exact computational_typing_of_strong_earlier heq hcon hqpat hTle
    (fun hΓ hp => hcov (hpats ▸ hp) hΓ)
    ((H.mono hET).strong hWT.orderedStrong hΓT) hΓenv

/-- Closed earlier declaration equations specialize at arbitrary universe
levels and weaken into any ambient well-formed context as computation chains. -/
theorem stage_types_computational_chains
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hstage : env₀ ∈ env.stages) (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    (hcov : ∀ {p r}, env₀.pats p r → ComputationalPatternCoverage EnvironmentCore.definitions p r) :
    ∀ {base E : VEnv}, base ≤ env₀ → base.addConstVals decl.typeConstants = some E →
      ∀ {A B : VExpr}, E.IsDefEqU decl.uvars [] A B → ∀ {Γ' : List VExpr} {cls : List VLevel},
        OnCtx Γ' (env.IsType univs) → (∀ l ∈ cls, l.WF univs) → cls.length = decl.uvars →
        TypedComputationEqU EnvironmentCore.definitions Γ' (A.instL cls) (B.instL cls) := by
  intro base E hbase hE A B hAB Γ' cls hΓ' hcls _
  obtain ⟨T, hd⟩ := hAB
  have hd' : E.IsDefEq univs [] (A.instL cls) (B.instL cls) (T.instL cls) := hd.instL hcls
  have HC := (stage_types_computational_typing (Γ := []) heq hcon hqpat hstage hdecl hadd hle hcov
    hbase hE trivial hd').1
  have hcl := HC.defeq.closedN' henv.ordered.closed ⟨⟩
  have HL := HC.liftN (Γ := []) heq EnvironmentCore.sound trivial hΓ'
    (n := Γ'.length) (k := 0) (by simpa using Ctx.LiftN.zero Γ' (n := Γ'.length) (Γ := []) rfl)
  exact ⟨_, by simpa only [hcl.1.liftN_eq (Nat.zero_le _),
    hcl.2.1.liftN_eq (Nat.zero_le _)] using HL⟩

end Lean4Lean.VEnv.Strengthening
