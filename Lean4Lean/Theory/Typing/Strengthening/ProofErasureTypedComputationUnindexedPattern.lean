import Lean4Lean.Theory.Typing.Strengthening.UnindexedSingletonEquationInstance
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationSingletonEquation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationPatterns

/-! # Actual unindexed singleton patterns compute

The right instance's typing and the generic equation chain type the reconstructed
left instance. Its function prefix is the original one, and proof irrelevance
aligns its reconstructed major with the original proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params] {D : PureObservation.Definitions}

/-- A registered recursor occurrence at source level zero has a proof major.
This uses the registered family type, including restoration, rather than any
particular typing assigned to the major by the application derivation. -/
theorem registered_major_isProof
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (ht : env.HasType univs Γ (.app (mkApps (.const data.name ls) vs) M) T)
    (hlen : vs.length = data.majorOffset)
    (hz : (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero) : IsProof Γ M := by
  obtain ⟨hw, hlw, args, hMt⟩ := H.major_type henv hΓ ht hlen
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, hu, hl, _, _, hadd, _, he, -⟩ := H
  have hle : base ≤ env := hbase.trans ((addInduct_le hadd).trans he)
  have hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := fun family hf =>
    he.constants (addInduct_type_find hadd hf)
  obtain ⟨_, _, hadm⟩ := hdata.admissible
  have hlevels' : ∀ l ∈ data.levels.map (·.inst ls), l.WF univs := by
    intro l hlm
    obtain ⟨l0, _, rfl⟩ := List.mem_map.mp hlm
    exact VLevel.WF.inst hw
  have hlen' : (data.levels.map (·.inst ls)).length = data.schema.signature.uvars := by
    rw [List.length_map, hl]; exact hadm.levels_length
  obtain ⟨domains, level, hH, hlevel⟩ := hdata.family_head_type hprior henv hΓ hle hconstants
    data.owner hlevels' hlen'
  rw [Restoration.headLevels_inst, ← hr] at hH
  have ⟨_, hTs⟩ := hMt.isType henv.ordered hΓ
  have hlength := HasType.mkApps_sort_arity henv hΓ hH hTs
  have hsortT := (HasType.mkApps_wrapForalls henv hΓ hH ⟨_, hTs⟩ hlength).2
  rw [VExpr.instOuter_sort] at hsortT
  have hzero : level ≈ .zero := by
    have hz' : data.schema.signature.families[data.owner].resultLevel.inst
        (data.levels.map (·.inst ls)) ≈ .zero := by
      simpa only [InductiveSignature.RecursorSchema.sourceLevel, VLevel.inst_inst] using hz
    exact hlevel.trans hz'
  have hwlevel := (hsortT.isType henv.ordered hΓ).choose_spec.sort_inv henv.ordered
  exact ⟨_, hMt, hsortT.defeqU_r henv hΓ ⟨_, .sortDF hwlevel (by trivial) hzero⟩⟩

/-- Every actual unindexed singleton pattern at a proposition source has a
computation chain in the presentation selecting the environment registry. The
semantic premises are canonical equality, sound ordinary definitions, and the
source and reduct typings already in the pat rule. -/
theorem TypedComputationEq.unindexed_singleton_pattern
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData = env.recursorRegistry)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.pats p r)
    (hreg : env.recursorRegistry p.headConst = some data)
    (hlarge : data.largeTarget = true) (hn : data.numIndices = 0)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero)
    (hm : p.Matches t m1 m2) (ht : env.HasType univs Γ t T)
    (hr : env.HasType univs Γ (r.1.apply m1 m2) T) :
    TypedComputationEq D Γ t (r.1.apply m1 m2) T := by
  have hentry := recursorRegistry_entry hreg
  obtain ⟨decl, env₀, env₁, rec, hAt, _, hrec, _, hdname, _, covers⟩ := hentry
  obtain ⟨index, equation, ru, howner, hgen, hru, hof, hc, e, he⟩ := covers p r hp rfl
  subst e
  have he' : r = _ := he
  subst he'
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, happly⟩ :=
    SimplePattern.iotaRHS_apply_of_matches (k := rec.numParams + rec.numMotives + rec.numMinors)
      (nind := rec.numIndices) (cnp := ru.ctorParams) (nf := ru.nfields) (rhs := ru.rhs)
      (hc := hc) hm
  have H := hAt.registered
  have hmo : data.majorOffset = rec.getMajorIdx :=
    henv.recursorEntry_majorOffset hp
      (by simpa [SimplePattern.iota_headConst] using recursorRegistry_entry hreg)
  have hdn : data.name = rec.name := hdname.trans (by simp [SimplePattern.iota_headConst])
  have ht' : env.HasType univs Γ (.app (mkApps (.const data.name m1) recArgs)
      (mkApps (.const ru.ctor lsC) ctorArgs)) T := by
    rw [hdn]; simpa [mkApps_append] using ht
  obtain ⟨hw, hlen, _⟩ := H.major_type henv hΓ ht' (h1.trans hmo.symm)
  have F := RecursorData.singletonSignature H hlarge (packed := m1) hzero
  have hpe := H.patEquation_of_empty henv F.restoration hgen
  obtain ⟨hlT, hrT⟩ := H.equation_typed hgen
  have hl : m1.length = equation.uvars := hlen.trans (H.equation_uvars' hgen).symm
  have hlookup : Params.recursorData data.name = some data := by
    rw [hregistry]
    rw [hdn]; simpa [SimplePattern.iota_headConst] using hreg
  have HE := TypedComputationEq.unindexed_singleton_equation (D := D) heq hs hΓ hlookup H
    howner hgen hpe hlT hrT hw hl hlarge hn hzero
  have hrhs : (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2 =
      mkApps (equation.rhs.instL m1)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
    rw [hof.1]; exact happly
  rw [hrhs] at hr ⊢
  obtain ⟨major, HB⟩ := singletonInstance_unindexed_beta hAt hrec hru hgen hof hlarge hzero
    hn hlen h1 h2
  have hproof := registered_major_isProof hΓ H ht' (h1.trans hmo.symm) hzero
  rw [hdn] at ht'
  simpa only [mkApps_snoc] using
    HE.apply_equation_at_proof_major hΓ ht' hr hproof HB

/-- Missing indexed singleton coverage: actual proposition-source singleton
patterns with a nonempty index telescope must have typed computation chains.
Unindexed patterns are already covered above. This premise still does not
provide the separate type-fork joining needed for strengthening. -/
def TypedIndexedSingletonPatternChainClosure (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures data},
    OnCtx Γ (env.IsType univs) → env.pats p r →
    env.recursorRegistry p.headConst = some data → data.largeTarget = true →
    data.numIndices ≠ 0 → (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero →
    p.Matches e ls captures → env.HasType univs Γ e A →
    env.HasType univs Γ (r.1.apply ls captures) A →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- Only indexed singleton patterns remain in raw singleton chain coverage.
Registry selection is the standard concrete presentation, not a confluence
hypothesis; the unindexed branch is discharged by the proved construction. -/
theorem TypedIndexedSingletonPatternChainClosure.singleton_closure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData = env.recursorRegistry)
    (HI : TypedIndexedSingletonPatternChainClosure D) : TypedSingletonPatternChainClosure D := by
  intro Γ p r e A ls captures data hΓ hp hreg hl hz hm ht hr
  by_cases hn : data.numIndices = 0
  · exact TypedComputationEq.unindexed_singleton_pattern heq hs hregistry hΓ hp hreg hl hn hz hm ht hr
  · exact HI hΓ hp hreg hl hn hz hm ht hr

/-- Conditional ordinary chain completeness now needs only indexed singleton
coverage. Type-fork joining remains an independent open obligation, so this is
not a claimed strictly smaller sufficient strengthening condition. -/
theorem TypedComputationEq.of_defeq_of_indexed_singleton_closure
    (heq : env.HasCanonicalEq) (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HI : TypedIndexedSingletonPatternChainClosure EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A :=
  TypedComputationEq.of_defeq_of_singleton_closure heq hcon hqpat hguard
    (HI.singleton_closure heq EnvironmentCore.sound hregistry) hΓ H

end Lean4Lean.VEnv.Strengthening
