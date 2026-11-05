import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonIndexFormation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalStageTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalGenericDomains

/-! # Computational constructor-index typing before installing the rules

Formation of the generated recursor type supplies ordinary generic index
typings. Interpreting their strong derivations in the ambient environment needs
coverage only for the earlier registry. No type-fork joining is used here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- An earlier environment's recursor type formation gives ambient
computational typings for every generic constructor index. A caller must still
identify that earlier environment and supply coverage of its pattern registry. -/
theorem computational_indices_of_earlier_formation
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    {E : VEnv} (hE : E ≤ env) (hEW : E.WF)
    (hcov : ∀ {p r}, E.pats p r → ComputationalPatternCoverage EnvironmentCore.definitions p r)
    {s : InductiveSignature} (g : Instance s) (hu : g.uvars = univs)
    (hfam : s.families.size = 1) (hcs : s.constructors.size = 1)
    (owner : Fin s.families.size) (index : Fin s.constructors.size)
    {c : Constructor s.families.size} (hc : s.constructors[index] = c)
    (htarget : g.targetLevel = .zero)
    (H : E.IsType g.uvars [] (g.recursorType owner))
    (harity : (g.ctorIndicesAt c).length = (g.indicesAt owner).length) :
    OnCtx (g.params ++ g.fieldsAt c).reverse (env.IsType univs) ∧
      ComputationalTelInst EnvironmentCore.definitions (g.params ++ g.fieldsAt c).reverse
        (g.params ++ g.indicesAt owner)
        (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++ g.ctorIndicesAt c) := by
  obtain ⟨hctx, HT⟩ := g.singleton_indices_of_type_formation hEW hfam hcs owner index hc htarget H harity
  rw [hu] at hctx HT
  have hctx' : OnCtx (g.params ++ g.fieldsAt c).reverse (env.IsType univs) :=
    OnCtx.mono (fun ⟨u, H⟩ => ⟨u, H.mono hE⟩) hctx
  refine ⟨hctx', HT.1, fun j hj hd => ?_⟩
  exact (computational_typing_of_strong_earlier heq hcon hqpat hE
    (fun hΓ hp => hcov hp hΓ)
    ((HT.2 j hj hd).strong hEW.orderedStrong hctx) hctx').2.1

end Lean4Lean.VEnv.Strengthening
