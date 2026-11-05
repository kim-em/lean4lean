import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordObservation

/-! # Joint record observations with dependent family certificates

The new record-type leaf uses independent dependent rigid-head evidence.
Its proof-domain control frames need no positive closed domain approximation.
-/
namespace Lean4Lean.VEnv.Strengthening.DependentRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- Supplying the demanded term observations substitutes through both bodies
and dependent type annotations. Exact recovery of an image's assigned type is
not a premise. -/
theorem Obs.subst (H : Obs unit record parameter uc ctor family Δ S e key)
    (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i key, S i key → key.Valid unit record → Obs unit record parameter uc ctor family Δ' T (σ i) key) :
    Obs unit record parameter uc ctor family Δ' T (e.subst σ) key := by
  induction H generalizing Δ' T σ with
  | var _ HK h => exact hσ _ _ h HK
  | unit_ctor HT => exact .unit_ctor (HT.subst W)
  | record_ctor HT => exact .record_ctor (HT.subst W)
  | family HT => exact .family (HT.subst W)
  | family_type HE => exact .family_type (HE.subst W)
  | record_type HE HR =>
    exact .record_type (HE.subst W) (HR.subst W (by intro i t k h; cases h))
  | unit_type HE => exact .unit_type (HE.subst W)
  | univ HK HE => exact .univ HK (HE.subst W)
  | app HT _ _ ihf iha => exact .app (HT.subst W) (ihf W hσ) (fun key hk => iha key hk W hσ)
  | @lam Δ A b domain keys result S HT HE HK _ _ ihA ihb =>
    have HE' := HE.subst W
    have SD : DomainSort Δ A domain.level := HE.typing
    refine .lam (HT.subst W) HE' HK (fun key hk => ihA key hk W hσ) (ihb W.cons ?_)
    intro i key hi HV
    cases i with
    | zero => exact .var (by rw [HK key hi]; exact HE'.fresh) HV hi
    | succ i => exact (hσ i key hi HV).lift (W.sort SD)
  | @pi Δ A B domain keys result S HT HE HK _ _ ihA ihb =>
    have HE' := HE.subst W
    have SD : DomainSort Δ A domain.level := HE.typing
    refine .pi (HT.subst W) HE' HK (fun key hk => ihA key hk W hσ) (ihb W.cons ?_)
    intro i key hi HV
    cases i with
    | zero => exact .var (by rw [HK key hi]; exact HE'.fresh) HV hi
    | succ i => exact (hσ i key hi HV).lift (W.sort SD)

/-- Context conversion fixes the raw term and all finite keys. -/
theorem Obs.context (H : Obs unit record parameter uc ctor family Δ S e key)
    (W : ContextSubstitution Δ Δ' Subst.id) : Obs unit record parameter uc ctor family Δ' S e key := by
  simpa only [ProofShape.subst_id] using H.rename W (fun i key hi => ⟨i, rfl, hi⟩)

/-- A root beta contraction substitutes the observed argument into the body
and every demanded native-type annotation stored in it. -/
theorem Obs.beta_forward (H : Obs unit record parameter uc ctor family Δ S (.app (.lam A b) a) key)
    (HS : S.Typed unit record Δ) : Obs unit record parameter uc ctor family Δ S (b.inst a) key := by
  cases H with
  | family_type HE => exact .family_type (HE.beta .beta)
  | record_type HE HR =>
    exact .record_type (HE.beta .beta) (HR.beta_forward (by intro i t k h; cases h))
  | unit_type HE => exact .unit_type (HE.beta .beta)
  | univ HK HE => exact .univ HK (HE.beta .beta)
  | app HT HF HX =>
    cases HF with
    | lam _ _ _ _ HB =>
      have R := HB.subst HT.beta_interpretation (T := S) (fun i key hi HV => by
        cases i with
        | zero => exact HX key hi
        | succ i => exact .var (HS i key hi) HV hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

/-- A literal recovered Pi exposes the very input keys and dependent result
key requested by the function. Empty demand lists do not forget the input
carrier, which is explicitly retained in the key. -/
theorem Obs.pi_parts
    (H : Obs unit record parameter uc ctor family Δ S (.forallE A B) (.type (.fn domain keys result))) :
    TypeEquality Δ A domain ∧ (∀ key ∈ keys, key.control unit record = domain) ∧
      (∀ key ∈ keys, Obs unit record parameter uc ctor family Δ S A (.type key)) ∧
      Obs unit record parameter uc ctor family (A :: Δ) (Sets.cons keys S) B (.type result) := by
  cases H with
  | pi _ HE HK HA HB => exact ⟨HE, HK, HA, HB⟩
  | family_type HE =>
    obtain ⟨HD, HB⟩ := HE.pi_parts
    exact ⟨HD, by simp, by simp, .univ (by simp only [Key.Valid]) HB⟩

/-- Supplying the demanded values instantiates an observed native Pi's result.
This is the application case needed by native recovery: the current argument
may lack an exact native certificate for the Pi's displayed domain. -/
theorem Obs.pi_instantiate
    (H : Obs unit record parameter uc ctor family Δ S (.forallE A B) (.type (.fn domain keys result)))
    (W : ContextSubstitution (A :: Δ) Δ (Subst.one a))
    (HX : ∀ key ∈ keys, Obs unit record parameter uc ctor family Δ S a key)
    (HS : S.Typed unit record Δ) : Obs unit record parameter uc ctor family Δ S (B.inst a) (.type result) := by
  have HB := H.pi_parts.2.2.2
  have R := HB.subst W (T := S) (fun i key hi HV => by
    cases i with
    | zero => exact HX key hi
    | succ i => exact .var (HS i key hi) HV hi)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

end Lean4Lean.VEnv.Strengthening.DependentRecordDemand
