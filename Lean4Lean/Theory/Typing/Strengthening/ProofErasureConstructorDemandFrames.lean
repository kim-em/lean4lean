import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaLambdaResidual

/-! # Native control frames retain their input type demands

Actual native guards supply ordinary typing. Their type observations, when
available, supply the additional annotation provenance needed by identity and
eta. Those observations are explicit premises here, not inferred from typing.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- Constant wrapping introduces an unused domain, hence no new type demand
on its arbitrary argument. The body's value and annotation demands are lifted. -/
theorem Obs.constant_expansion (H : Obs unit record uc ctor family Δ S source key) :
    Obs unit record uc ctor family Δ S (constantExpansion source) key := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro H.typing.ne_proof))
  exact .app (keys := []) HT (.lam HF (lambda_domain_equality HF) (by simp) (by simp) (H.lift SD)) (by simp)

/-- A native identity is observed when its selected annotation carries the
source's native-type demand. This is the annotation premise missing from the
ordinary body-only observer. -/
theorem Obs.identity_of_type_observation (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs unit record uc ctor family Δ S source key)
    (RN : ScopedTypeRecovery Step Δ source A)
    (HA : Obs unit record uc ctor family Δ S A (.type key)) :
    Obs unit record uc ctor family Δ S (.app (.lam A (.bvar 0)) source) key := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base (.intro RN))
  have HF := H.typing.identity_frame hstep RN
  have HE := TypeEquality.of_native hstep H.typing RN
  refine .app (keys := [key]) HT (.lam HF HE ?_ ?_ (.var HE.fresh H.valid (by simp [Sets.cons]))) ?_
  · intro k hk; obtain rfl := List.mem_singleton.1 hk; rfl
  · intro k hk; obtain rfl := List.mem_singleton.1 hk; exact HA
  · intro k hk; obtain rfl := List.mem_singleton.1 hk; exact H

/-- Observing the selected native Pi supplies both the actual eta domain's
input demands and the retained fresh argument keys. No annotation is frozen
at the original written domain. -/
theorem Obs.eta_of_type_observation (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs unit record uc ctor family Δ S source (.fn domain keys result))
    (RN : ScopedTypeRecovery Step Δ source (.forallE A B)) (SD : DomainSort Δ A u)
    (HP : Obs unit record uc ctor family Δ S (.forallE A B) (.type (.fn domain keys result))) :
    Obs unit record uc ctor family Δ S (.lam A (.app (source.liftN 1) (.bvar 0)))
      (.fn domain keys result) := by
  have HEta : NativeEtaExpansion Step Δ source (.lam A (.app (source.liftN 1) (.bvar 0))) := by
    have E : etaArgument u = .bvar 0 := if_neg (H.typing.eta_domain_ne_zero hstep RN SD)
    simpa only [E] using NativeEtaExpansion.intro RN SD
  obtain ⟨A', E, HT, HB, HX, v, SA⟩ := H.typing.eta_parts hstep HEta
  cases ProofShape.lam.inj E |>.1
  have HK : ∀ key ∈ keys, key.Valid unit record := by
    have HV := H.valid
    simp only [Key.Valid] at HV
    exact fun key hk => (HV.1 key hk).2
  obtain ⟨HE, HC, HA, _⟩ := HP.pi_parts
  exact .lam HT HE HC HA (.app HB (H.lift SA)
    (fun key hk => .var (by rw [HC key hk]; exact HX) (HK key hk) hk))

/-- Missing conversion-tail preservation and body native coverage are explicit
induction premises. They suffice for native recovery of an observed lambda,
including every selected body type and the full native conversion tail. -/
theorem lambda_native_of_type_preservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcomp : ∀ {a b key}, ScopedCompute Step Δ a b →
      Obs unit record uc ctor family Δ S a (.type key) → Obs unit record uc ctor family Δ S b (.type key))
    (H : Obs unit record uc ctor family Δ S (.lam A b) (.fn domain keys result))
    (HB : ∀ {T}, ScopedTypeRecovery Step (A :: Δ) b T →
      Obs unit record uc ctor family (A :: Δ) (Sets.cons keys S) T (.type result))
    (RN : ScopedTypeRecovery Step Δ (.lam A b) out) :
    Obs unit record uc ctor family Δ S out (.type (.fn domain keys result)) := by
  obtain ⟨C, RC, RP⟩ := RN.lam_compute
  cases H with
  | lam HT HE HK HA _ =>
    exact hcomp RP (.pi (TypeEquality.of_native hstep HT (.lam RC)).typing HE HK HA (HB RC))

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
