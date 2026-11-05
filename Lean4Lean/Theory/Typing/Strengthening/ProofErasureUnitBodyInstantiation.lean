import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitReturn

/-! # Arbitrary dependent bodies at computed unit arguments

The complete unit readout supplies a constructor-reaching path for every
computed image of a looked-up unit variable. Constructor recovery then repairs
instantiation of any generic body computation, beyond the neutral family body
used to establish the readout. The argument itself needs no native certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Any computed image of a looked-up unit variable can instantiate arbitrary
generic body computation up to an explicit common result. The body may be data,
a type, a function, or a proof, and may depend arbitrarily on the unit binder.
Only the argument's origin is restricted; no native image premise remains. -/
theorem static_structure_unit_body_instantiation_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const family []))
    (ht : env.HasType univs Γ x (.const family []))
    (hb : env.HasType univs (.const family [] :: Γ) b B)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ x))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.const family [] :: Γ)) (proofErase (.const family [] :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) (out.inst (.const info.ctorName [])) := by
  have RC := static_structure_unit_variable_return heq hs hi hp hx hz hD hS hΓ hl RX
  have hΓS : OnCtx (.const family [] :: Γ) (env.IsType univs) :=
    ⟨hΓ, .succ u, hS.weak0 henv.ordered⟩
  exact static_structure_inst_join_constructor (params := []) (images := []) heq hs hi hx
    (by simp [hp, hz]) hΓS hb ht (by simp) RC RB

/-- The body and a computed unit argument can evolve independently. Full
unit readout returns the current argument to the constructor, so the generic
body's instantiated output joins the original contractum without HJ or HF. -/
theorem static_structure_unit_body_argument_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const family []))
    (ht : env.HasType univs Γ x (.const family []))
    (hb : env.HasType univs (.const family [] :: Γ) b B)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ x))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.const family [] :: Γ)) (proofErase (.const family [] :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst image) (out.inst (.const info.ctorName [])) := by
  have RC := static_structure_unit_variable_return heq hs hi hp hx hz hD hS hΓ hl (RX.trans RA)
  have hΓS : OnCtx (.const family [] :: Γ) (env.IsType univs) :=
    ⟨hΓ, .succ u, hS.weak0 henv.ordered⟩
  exact static_structure_body_argument_join_constructor (params := []) (images := []) heq hs hi hx
    (by simp [hp, hz]) hΓS hb ht (by simp) RA RC RB

/-- Different computed unit inhabitants may be supplied to independently
computed bodies with a common generic output. Both instantiated programs reach
that output at the same constructor, without native recovery of either image. -/
theorem static_structure_unit_paired_body_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (ht : env.HasType univs Γ x (.const family []))
    (ht' : env.HasType univs Γ y (.const family []))
    (hb : env.HasType univs (.const family [] :: Γ) b B)
    (hb' : env.HasType univs (.const family [] :: Γ) b' B')
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ x))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar j)) (proofErase Γ y))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.const family [] :: Γ)) (proofErase (.const family [] :: Γ) b) out)
    (RB' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.const family [] :: Γ)) (proofErase (.const family [] :: Γ) b') out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b'.inst y)) (out.inst (.const info.ctorName [])) :=
  ⟨(static_structure_unit_body_instantiation_join heq hs hi hp hx hz hD hS hΓ hli ht hb RX RB).1,
    (static_structure_unit_body_instantiation_join heq hs hi hp hx hz hD hS hΓ hlj ht' hb' RY RB').1⟩

end Lean4Lean.VEnv.Strengthening
