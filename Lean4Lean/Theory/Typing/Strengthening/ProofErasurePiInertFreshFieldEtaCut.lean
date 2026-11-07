import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldEtaComponent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorFieldAncestry

/-! # A minimum empty-prefix eta body must supply its fresh field

The existing counted body cut already records the enclosing consuming beta.
Its singleton component ancestry and the two-eta replay exclude a nested
root at the empty constructor prefix. The same selected native function root
therefore has the original fresh field in its constructor prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private eta_argument_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut
variable [Params] {D : Definitions}

private theorem fresh_singleton_fixed
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) [etaArgument u] args) :
    args = [etaArgument u] := by
  cases HA with
  | cons RX rest =>
    cases rest
    rw [eta_argument_fixed RX]

/-- In a global minimum, eta on the empty constructor prefix of a pair must
reach a nested function-eta root that already contains its fresh type field.
A root on the empty prefix would save either the inner or outer eta charge.
This refines the very same body cut, preserving its exact histories and
continuation. It does not yet prove original-field readout after that fresh
field is instantiated by the enclosing beta. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_supplies_fresh_field
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (harity : info.nparams + info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args out ct
      (ConstructorEtaBodyRoot D))
    (HK : K out ck) (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → cost ≤ j+k) :
    CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args out ct
      (fun m Ξ source target => source = .app (.const info.ctorName []) (etaArgument u) ∧
        ∃ k, k < m ∧ NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target) := by
  have HF := H.unsaturated_function_root heq hs hi (by simp only [List.length_nil, harity]; omega)
  obtain ⟨domain, body, x, xs, cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RBodyPrefix, HR, HN, RT, HBodyMin, HJointMin,
    HI, HTR, WI, HC, HG⟩ := HF
  cases HL
  have Eargs : bodyPre ++ bodyPending = [etaArgument u] :=
    fresh_singleton_fixed (by simpa only [List.map_nil, List.nil_append] using HA.1)
  refine ⟨domain, body, x, xs, cf, ca, cs, cd, cb, m, [], bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, .nil, HA, RBodyPrefix, HR, HN, RT, HBodyMin, HJointMin,
    HI, HTR, WI, HC, ?_, HG⟩
  cases bodyPre with
  | nil =>
    have EP : bodyPending = [etaArgument u] := by simpa only [List.nil_append] using Eargs
    obtain ⟨k, _, HE⟩ := HG
    cases HE with
    | intro RN' SD' =>
      exact (pi_inert_pair_nested_eta_outer_consumption_not_minimal
        heq hs hi hu hshape SD RN RN' SD' HT RP RD
        (by simpa only [EP, ProofShape.mkApps, ProofShape.liftN] using RT)
        RX RS HK (by omega) HM).elim
  | cons first rest =>
    have hlen := congrArg List.length Eargs
    have EP : bodyPending = [] := List.eq_nil_of_length_eq_zero (by simp only
      [List.length_append, List.length_cons, List.length_nil] at hlen; omega)
    have EPre : first :: rest = [etaArgument u] := by simpa only [EP, List.append_nil] using Eargs
    rw [EPre]
    rfl

end Lean4Lean.VEnv.Strengthening
