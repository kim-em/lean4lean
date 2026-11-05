import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorUnitNativeReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-! # Family ancestry through repeated constructor expansions

Each round permits arbitrary full computations in the parameter and dependent
fields, or an actual native structure expansion with an independently selected
guard. The family ancestry invariant survives every finite sequence of rounds.
This grammar does not yet cover arbitrary computations of the whole major.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private const_spine_inj from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- Two registered families recovered at the same typed source have the same
head and arity. A monomorphic selection forces every other selection to be
monomorphic as well; no common native type or type-fork premise is required. -/
theorem native_registered_family_shape
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections r info) (hi' : env.projections r' info')
    (RA : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const r []) ps))
    (RB : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const r' ls') qs)) :
    r = r' ∧ ls' = [] ∧ ps.length = qs.length := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht RA
  obtain ⟨B, heB, EB⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht RB
  obtain ⟨as, rfl, rfl⟩ := proofErase_const_spine_inv EA
  obtain ⟨bs, rfl, rfl⟩ := proofErase_const_spine_inv EB
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  obtain ⟨E, HL, HA⟩ := henv.headInversion.rigid_rigid hΓ
    (henv.projectionRigid hi) (henv.projectionRigid hi')
    ((heA.uniqU henv hΓ heB).typeChain henv hΓ hA)
  cases HL
  exact ⟨E, rfl, by simpa only [List.length_map] using HA.length_eq⟩

/-- A typed constructor image together with a forward computation from a
fixed family origin to its current literal parameter. The existential typing
is preserved by ordinary computation realization, not by exact native typing. -/
def ConstructorFamilyState (D : PureObservation.Definitions) (Γ : List VExpr)
    (r : Name) (info : VProjectionInfo) (origin source : ProofShape) : Prop :=
  ∃ e T p fields,
    env.HasType univs Γ e T ∧ proofErase Γ e = source ∧
    source = ProofShape.mkApps (.const info.ctorName []) (p :: fields) ∧
    fields.length = info.numFields ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      origin (.app (.const r []) p)

/-- An arbitrary whole-term computation can enter the constructor invariant.
Only the endpoint parameter's family ancestry is supplied separately; the
source need not itself be a constructor or have any native certificate. -/
theorem ConstructorFamilyState.of_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hf : fields.length = info.numFields)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const info.ctorName []) (p :: fields)))
    (RO : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      origin (.app (.const r []) p)) :
    ConstructorFamilyState D Γ r info origin
      (ProofShape.mkApps (.const info.ctorName []) (p :: fields)) := by
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl rfl RE
  exact ⟨e', T, p, fields, HE.hasType.2, Ee', rfl, hf, RO⟩

/-- A typed family application to a unit variable supplies the initial origin
when a whole computation reaches a constructor whose parameter descends from
that variable. No constructor-field history or native guard is required. -/
theorem ConstructorFamilyState.of_unit_parameter_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family [])) (hf : fields.length = info.numFields)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) p)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const info.ctorName []) (p :: fields))) :
    ConstructorFamilyState D Γ r info
      (proofErase Γ (.app (.const r []) (.bvar i)))
      (ProofShape.mkApps (.const info.ctorName []) (p :: fields)) := by
  have hFi := HasType.app hF (HasType.bvar hl)
  have EE : proofErase Γ (.app (.const r []) (.bvar i)) =
      .app (.const r []) (proofErase Γ (.bvar i)) := by
    simpa [VExpr.mkApps, ProofShape.mkApps] using proofErase_const_spine
      (c := r) (ls := []) (args := [.bvar i]) hΓ hFi (not_isProof_of_sort hΓ hFi)
  apply ConstructorFamilyState.of_compute heq hs hΓ ht hf RE
  rw [EE]
  exact .app .refl RP

/-- The computed-header certificate transfers the state's family ancestry to
every native output, including conversions at any intermediate application. -/
theorem ConstructorFamilyState.native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFamilyState D Γ r info origin source)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) origin out := by
  obtain ⟨e, T, p, fields, ht, Ee, Es, hfields, RO⟩ := H
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv (Ee.trans Es)
  cases args with
  | nil => cases Eargs
  | cons a args =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj Eargs
    have hf : args.length = info.numFields := by simpa using hfields
    rw [Es] at RN
    exact RO.trans (registered_computed_header_raw_origin heq hs hΓ hi hx HH
      (args := [a]) (by simpa using hp.symm) hf ht
      (List.Forall₂.rfl (fun _ _ => .refl)) (List.Forall₂.rfl (fun _ _ => .refl)) RN)

/-- Independent full computations of all constructor arguments preserve the
family ancestry invariant, including dependencies between retained fields. -/
theorem ConstructorFamilyState.arguments
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorFamilyState D Γ r info origin
      (ProofShape.mkApps (.const info.ctorName []) (p :: fields)))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p q)
    (RF : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      fields fields') :
    ConstructorFamilyState D Γ r info origin
      (ProofShape.mkApps (.const info.ctorName []) (q :: fields')) := by
  obtain ⟨e, T, p', fs, ht, Ee, Es, hf, RO⟩ := H
  obtain ⟨rfl, rfl⟩ := List.cons.inj (const_spine_inj Es).2.2
  have R := ScopedCompute.mkApps (ScopedCompute.refl (e := ProofShape.const info.ctorName []))
    (List.Forall₂.cons RP RF)
  rw [← Ee] at R
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl rfl R
  exact ⟨e', T, q, fields', HE.hasType.2, Ee', rfl,
    RF.length_eq.symm.trans hf, RO.trans (.app .refl RP)⟩

/-- An actual structure expansion preserves family ancestry even when its
native guard independently selects new parameters. Family and universe shape
are derived from the source typing, rather than imposed on the expansion. -/
theorem ConstructorFamilyState.expand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFamilyState D Γ r info origin source)
    (RE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source target) :
    ConstructorFamilyState D Γ r info origin target := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) := erased_static_structure_eta_expansion_union_descent heq hs
  obtain ⟨e, T, p, fields, ht, Ee, Es, hf, RO⟩ := H
  have RN := computed_constructor_image_native (Target := ErasedStaticStructureEtaExpansionUnion D)
    hstep hΓ hi hx (images := p :: fields) (by simp [hp, hf, Nat.add_comm]) ht
    (show ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const info.ctorName []) (p :: fields)) from
      by rw [Ee, Es]; exact .refl)
  have RS : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source target :=
    .base (erased_static_structure_eta_expansion_union_structure RE)
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize hstep hΓ ht rfl rfl (Ee ▸ RS)
  cases RE with
  | @intro r' info' ls _ qs hi' hx' ha hq RG =>
    rw [← Es, ← Ee] at RN
    rw [← Ee] at RG
    obtain ⟨rfl, rfl, _⟩ := native_registered_family_shape hstep hΓ ht hi hi' RN RG
    cases henv.ordered.projections_unique hi hi'
    have hq' : qs.length = 1 := hq.trans hp
    cases qs with
    | nil => simp at hq'
    | cons q qs =>
      have Eq : qs = [] := by cases qs <;> simp_all
      subst qs
      refine ⟨e', T, q, (List.range info.numFields).map (nativeStructureField r info [] source),
        HE.hasType.2, Ee', rfl, by simp, ?_⟩
      exact ConstructorFamilyState.native_origin heq hs hΓ hi hp hx HH
        ⟨e, T, p, fields, ht, Ee, Es, hf, RO⟩ (Ee ▸ RG)

/-- Finite constructor rounds allow arbitrary computations inside arguments
and every actual structure expansion at the root. Other whole-major primitive
steps are not yet included in this grammar. -/
inductive ConstructorRounds (D : PureObservation.Definitions) (Δ : List ProofShape)
    (info : VProjectionInfo) : ProofShape → ProofShape → Prop where
  | refl : ConstructorRounds D Δ info a a
  | arguments (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ p q)
      (RF : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) fields fields') :
      ConstructorRounds D Δ info (ProofShape.mkApps (.const info.ctorName []) (p :: fields))
        (ProofShape.mkApps (.const info.ctorName []) (q :: fields'))
  | expand (RE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
      ConstructorRounds D Δ info a b
  | trans : ConstructorRounds D Δ info a b → ConstructorRounds D Δ info b c →
      ConstructorRounds D Δ info a c

/-- Constructor rounds are genuine computations in the full staged language. -/
theorem ConstructorRounds.compute (R : ConstructorRounds D Δ info a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b := by
  induction R with
  | refl => exact .refl
  | arguments RP RF => exact .mkApps .refl (.cons RP RF)
  | expand RE => exact .base (erased_static_structure_eta_expansion_union_structure RE)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Family ancestry survives unboundedly many rounds with independently chosen
native guards and arbitrary dependent field computations between rounds. -/
theorem ConstructorFamilyState.rounds
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFamilyState D Γ r info origin source)
    (R : ConstructorRounds D (proofEraseCtx Γ) info source target) :
    ConstructorFamilyState D Γ r info origin target := by
  induction R with
  | refl => exact H
  | arguments RP RF => exact H.arguments heq hs hΓ RP RF
  | expand RE => exact H.expand heq hs hΓ hi hp hx HH RE
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)

/-- Every selected native output after repeated constructor rounds returns to
the fixed unit-parameter family. The unit-family origin and computed-header
certificate are explicit, but no type-fork or common-native premise is used. -/
theorem constructor_rounds_unit_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : ConstructorFamilyState D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) source)
    (R : ConstructorRounds D (proofEraseCtx Γ) rinfo source target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) target out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  exact static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hR) hDr hΓ hF hl
    ((H.rounds heq hs hΓ hR hrp hrx HH R).native_origin heq hs hΓ hR hrp hrx HH RN)

/-- Native type histories from two independent sequences of constructor
rounds join at the canonical unit-family type, even after arbitrary subsequent
type computations. This is a type join for the stated grammar of major paths,
not a claim that every full computation is a sequence of constructor rounds. -/
theorem constructor_rounds_unit_native_histories_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : ConstructorFamilyState D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) source)
    (R₁ : ConstructorRounds D (proofEraseCtx Γ) rinfo source target₁)
    (R₂ : ConstructorRounds D (proofEraseCtx Γ) rinfo source target₂)
    (RN₁ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) target₁ out₁)
    (RN₂ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) target₂ out₂)
    (RC₁ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₁ left)
    (RC₂ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₂ right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.const info.ctorName [])) :=
  ⟨constructor_rounds_unit_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hΓ hF hl H R₁ (RN₁.convert RC₁),
    constructor_rounds_unit_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hΓ hF hl H R₂ (RN₂.convert RC₂)⟩

end Lean4Lean.VEnv.Strengthening
