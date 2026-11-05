import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordFrames

/-! # Joint demands through compatible computation

The native valuation is extended from observed binder annotations. Compatible
computation preserves all joint demands once its primitive roots preserve them.
This theorem handles beta, domain changes, and dependent Pi codomains; it does
not assume that the enriched primitive roots already satisfy the premise.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- Each demanded variable's actual oracle type carries its native-type key. -/
def Valuation (unit record : AtomicControl.Atom) (uc ctor family : Name) (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i key, S i key → Obs unit record uc ctor family Δ S (contextOracle Δ i) (.type key)

/-- The fresh oracle demand is the observed annotation, lifted once. Older
oracle observations lift by ordinary interpreted weakening. -/
theorem Valuation.cons (HV : Valuation unit record uc ctor family Δ S)
    (HE : TypeEquality Δ A domain)
    (HA : ∀ key ∈ keys, Obs unit record uc ctor family Δ S A (.type key)) :
    Valuation unit record uc ctor family (A :: Δ) (Sets.cons keys S) := by
  intro i key hi
  cases i with
  | zero => exact (HA key hi).lift HE.typing
  | succ i => exact (HV i key hi).lift HE.typing

/-- Primitive preservation lifts to all compatible computation. Lambda/Pi
annotation observations evolve by the same induction, and their dependent
body observations survive ordinary context conversion. Both input valuations
are explicit; no blanket native completeness or join assumption is hidden. -/
theorem Obs.compute (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed unit record Δ →
      Valuation unit record uc ctor family Δ S → Obs unit record uc ctor family Δ S a key →
      Obs unit record uc ctor family Δ S b key)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed unit record Δ)
    (HV : Valuation unit record uc ctor family Δ S)
    (H : Obs unit record uc ctor family Δ S source key) : Obs unit record uc ctor family Δ S out key := by
  induction R using ScopedCompute.rootBeta_induction generalizing S key with
  | refl => exact H
  | base R => exact hroot R HS HV H
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS HV (ih₁ HS HV H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | family_type HE => exact .family_type (HE.compute hstep (.app RF RX))
    | unit_type HE => exact .unit_type (HE.compute hstep (.app RF RX))
    | function_type HE => exact .function_type (HE.compute hstep (.app RF RX))
    | univ HK HE => exact .univ HK (HE.compute hstep (.app RF RX))
    | app _ HF HX => exact .app HT (ihf HS HV HF) (fun key hk => ihx HS HV (HX key hk))
  | proj R _ =>
    cases H with
    | family_type HE => exact .family_type (HE.compute hstep (.proj R))
    | unit_type HE => exact .unit_type (HE.compute hstep (.proj R))
    | function_type HE => exact .function_type (HE.compute hstep (.proj R))
    | univ HK HE => exact .univ HK (HE.compute hstep (.proj R))
  | lam RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    cases H with
    | family_type HE => exact .family_type (HE.compute hstep (.lam RA RB))
    | unit_type HE => exact .unit_type (HE.compute hstep (.lam RA RB))
    | function_type HE => exact .function_type (HE.compute hstep (.lam RA RB))
    | univ HK HE => exact .univ HK (HE.compute hstep (.lam RA RB))
    | lam _ HE HK HA HB =>
      exact .lam HT (HE.compute hstep RA) HK (fun key hk => ihA HS HV (HA key hk))
        ((ihb (HS.cons HE HK) (HV.cons HE HA) HB).context (HE.compute_context hstep RA))
  | forallE RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.forallE RA RB)
    cases H with
    | family_type HE => exact .family_type (HE.compute hstep (.forallE RA RB))
    | unit_type HE => exact .unit_type (HE.compute hstep (.forallE RA RB))
    | function_type HE => exact .function_type (HE.compute hstep (.forallE RA RB))
    | univ HK HE => exact .univ HK (HE.compute hstep (.forallE RA RB))
    | pi _ HE HK HA HB =>
      exact .pi HT (HE.compute hstep RA) HK (fun key hk => ihA HS HV (HA key hk))
        ((ihb (HS.cons HE HK) (HV.cons HE HA) HB).context (HE.compute_context hstep RA))

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
