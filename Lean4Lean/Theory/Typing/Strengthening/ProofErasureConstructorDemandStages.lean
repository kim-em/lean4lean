import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandPrimitives

/-! # Full-stage preservation of joint constructor demands

Finite-stage induction discharges native identity, function eta and record
structure expansion using native observation preservation at the preceding
stage. No arbitrary native-header or type-computation premise remains.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.const s []) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hTag hF

/-- Every actual enriched primitive stage preserves joint value/type demands.
The three rigid-head exclusions are automatic for EnvironmentCore definitions. -/
theorem stage_preserves
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs) :
    ∀ stage {Δ S a b key}, ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      Obs U RT uc c t Δ S a key → Obs U RT uc c t Δ S b key := by
  have hRU : env.Rigid uc := henv.projectionCtorRigid hi
  have hRC : env.Rigid c := henv.projectionCtorRigid hTag
  have hRF : env.Rigid t := henv.projectionRigid hTag
  intro stage
  induction stage with
  | zero =>
    intro Δ S a b key R HS HV H
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
      erased_static_structure_eta_expansion_stage_descent heq hs 0
    rcases R with (R | R) | R
    · exact H.rigid_primitive hstep (.inl (.inl R)) (erased_iota_primitive_head R)
        (erased_iota_primitive_no_rigid hRU huc R)
        (erased_iota_primitive_no_rigid hRC hc R)
        (erased_iota_primitive_no_rigid hRF hf R)
    · have RR : ErasedStaticStructureEtaExpansionStage D 0 Δ a b := .inl (.inr R)
      cases R with
      | sort =>
        cases H with
        | unit_type HE => exact .unit_type (HE.compute hstep (.base RR))
        | univ HK HE => exact .univ HK (HE.compute hstep (.base RR))
        | family_type HE => exact .family_type (HE.compute hstep (.base RR))
      | const HL hw =>
        cases H with
        | unit_type HE => exact .unit_type (HE.compute hstep (.base RR))
        | univ HK HE => exact .univ HK (HE.compute hstep (.base RR))
        | family_type HE => exact .family_type (HE.compute hstep (.base RR))
        | unit_ctor HT => cases HL; exact .unit_ctor HT
        | record_ctor HT => cases HL; exact .record_ctor HT
        | family HT => cases HL; exact .family HT
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ S a b key R HS HV H
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D (stage+1)) :=
      erased_static_structure_eta_expansion_stage_descent heq hs (stage+1)
    have hprev : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D stage) :=
      erased_static_structure_eta_expansion_stage_descent heq hs stage
    rcases R with R | R | R | R | R | R
    · exact ih R HS HV H
    · apply H.rigid_primitive hstep (.inr (.inl R)) R.2.head
      all_goals intro HH
      all_goals cases R.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
        first
        | exact V.not_rigid (hn ▸ hRU)
        | exact V.not_rigid (hn ▸ hRC)
        | exact V.not_rigid (hn ▸ hRF)
    · apply H.rigid_primitive hstep (.inr (.inr (.inl R))) R.head
      all_goals intro HH
      all_goals cases R with
      | intro _ =>
        obtain ⟨_, _, _, hp⟩ := heq.2.2.2
        first
        | exact hRU.pats _ _ hp (by
            simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)
        | exact hRC.pats _ _ hp (by
            simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)
        | exact hRF.pats _ _ hp (by
            simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)
    · exact H.registered_identity hi hS hTag hF hprev ih HS HV R
    · exact H.registered_eta hi hS hTag hF hprev ih HS HV R
    · exact H.registered_structure hi hS hTag hF hprev ih HS HV R

/-- Full compatible computation, including every structure-expansion and beta
interleaving, preserves the joint observer for the registered signature. -/
theorem Obs.full_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out) :
    Obs U RT uc c t Δ S out key :=
  H.compute (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ HS HV H => stage_preserves hi hS hTag hF heq hs huc hc hf stage R HS HV H) R HS HV

/-- Every selected full-union native output retains the corresponding type
key. Its parameter information survives all native conversion tails. -/
theorem Obs.full_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ source out) :
    Obs U RT uc c t Δ S out (.type key) :=
  H.registered_native hi hS hTag hF (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ HS HV H => stage_preserves hi hS hTag hF heq hs huc hc hf stage R HS HV H) HS HV RN

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
