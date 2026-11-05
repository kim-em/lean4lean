import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordFrames

/-! # Joint record observations with dependent family certificates

The new record-type leaf uses independent dependent rigid-head evidence.
Its proof-domain control frames need no positive closed domain approximation.
-/
namespace Lean4Lean.VEnv.Strengthening.DependentRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- Each demanded variable's actual oracle type carries its native-type key. -/
def Valuation (unit record : AtomicControl.Atom) (parameter : HeterogeneousControl.ControlType) (uc ctor family : Name) (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i key, S i key → Obs unit record parameter uc ctor family Δ S (contextOracle Δ i) (.type key)

/-- The fresh oracle demand is the observed annotation, lifted once. Older
oracle observations lift by ordinary interpreted weakening. -/
theorem Valuation.cons (HV : Valuation unit record parameter uc ctor family Δ S)
    (HE : TypeEquality Δ A domain)
    (HA : ∀ key ∈ keys, Obs unit record parameter uc ctor family Δ S A (.type key)) :
    Valuation unit record parameter uc ctor family (A :: Δ) (Sets.cons keys S) := by
  intro i key hi
  cases i with
  | zero => exact (HA key hi).lift HE.typing
  | succ i => exact (HV i key hi).lift HE.typing

/-- Independent rigid-family evidence must survive the chosen computation
relation. The concrete enriched stages discharge this using the dependent
rigid-head observer, with no joint native induction premise. -/
def FamilyPreserves (Step : List ProofShape → ProofShape → ProofShape → Prop) (family : Name) : Prop :=
  ∀ {Δ a b}, ScopedCompute Step Δ a b →
    RigidDemandProfile.Obs family 1 Δ (fun _ _ _ => False) a .sort .pi →
    RigidDemandProfile.Obs family 1 Δ (fun _ _ _ => False) b .sort .pi

/-- Primitive preservation lifts to all compatible computation. Lambda/Pi
annotation observations evolve by the same induction, and their dependent
body observations survive ordinary context conversion. Both input valuations
are explicit; no blanket native completeness or join assumption is hidden. -/
theorem Obs.compute (hstep : ErasedScopedPrimitiveDescent Step)
    (hfamily : FamilyPreserves Step family)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed unit record Δ →
      Valuation unit record parameter uc ctor family Δ S → Obs unit record parameter uc ctor family Δ S a key →
      Obs unit record parameter uc ctor family Δ S b key)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed unit record Δ)
    (HV : Valuation unit record parameter uc ctor family Δ S)
    (H : Obs unit record parameter uc ctor family Δ S source key) : Obs unit record parameter uc ctor family Δ S out key := by
  induction R using ScopedCompute.rootBeta_induction generalizing S key with
  | refl => exact H
  | base R => exact hroot R HS HV H
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS HV (ih₁ HS HV H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | record_type HE HR => exact .record_type (HE.compute hstep (.app RF RX)) (hfamily (.app RF RX) HR)
    | family_type HE => exact .family_type (HE.compute hstep (.app RF RX))
    | unit_type HE => exact .unit_type (HE.compute hstep (.app RF RX))
    | univ HK HE => exact .univ HK (HE.compute hstep (.app RF RX))
    | app _ HF HX => exact .app HT (ihf HS HV HF) (fun key hk => ihx HS HV (HX key hk))
  | proj R _ =>
    cases H with
    | record_type HE HR => exact .record_type (HE.compute hstep (.proj R)) (hfamily (.proj R) HR)
    | family_type HE => exact .family_type (HE.compute hstep (.proj R))
    | unit_type HE => exact .unit_type (HE.compute hstep (.proj R))
    | univ HK HE => exact .univ HK (HE.compute hstep (.proj R))
  | lam RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    cases H with
    | record_type HE HR => exact .record_type (HE.compute hstep (.lam RA RB)) (hfamily (.lam RA RB) HR)
    | family_type HE => exact .family_type (HE.compute hstep (.lam RA RB))
    | unit_type HE => exact .unit_type (HE.compute hstep (.lam RA RB))
    | univ HK HE => exact .univ HK (HE.compute hstep (.lam RA RB))
    | lam _ HE HK HA HB =>
      exact .lam HT (HE.compute hstep RA) HK (fun key hk => ihA HS HV (HA key hk))
        ((ihb (HS.cons HE HK) (HV.cons HE HA) HB).context (HE.compute_context hstep RA))
  | forallE RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.forallE RA RB)
    cases H with
    | record_type HE HR => exact .record_type (HE.compute hstep (.forallE RA RB)) (hfamily (.forallE RA RB) HR)
    | family_type HE => exact .family_type (HE.compute hstep (.forallE RA RB))
    | unit_type HE => exact .unit_type (HE.compute hstep (.forallE RA RB))
    | univ HK HE => exact .univ HK (HE.compute hstep (.forallE RA RB))
    | pi _ HE HK HA HB =>
      exact .pi HT (HE.compute hstep RA) HK (fun key hk => ihA HS HV (HA key hk))
        ((ihb (HS.cons HE HK) (HV.cons HE HA) HB).context (HE.compute_context hstep RA))

end Lean4Lean.VEnv.Strengthening.DependentRecordDemand
