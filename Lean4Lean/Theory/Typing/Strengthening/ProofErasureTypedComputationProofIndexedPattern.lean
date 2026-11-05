import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofIndexedSpine
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationProofIndexed

/-! # Actual singleton pattern coverage with dependent proof indices -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
variable [Params] {D : PureObservation.Definitions}

/-- Every actual singleton pattern with propositional indices has a typed
computation chain. Both full recursor spines retain the same parameter, motive
and minor captures; their differing indices and majors erase to proofs. No
joinable-typing or earlier-stage confluence premise is needed for alignment. -/
theorem TypedComputationEq.proof_indices_singleton_pattern
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData = env.recursorRegistry)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.pats p r)
    (hreg : env.recursorRegistry p.headConst = some data)
    (hlarge : data.largeTarget = true)
    (hS : data.singletonLayout env m1 = some S)
    (hindices : PropTelescope env univs (data.propParams m1).reverse S.indices)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero)
    (hm : p.Matches t m1 m2) (ht : env.HasType univs Γ t T)
    (hr : env.HasType univs Γ (r.1.apply m1 m2) T) :
    TypedComputationEq D Γ t (r.1.apply m1 m2) T := by
  have Hpat : env.IsDefEq univs Γ t (r.1.apply m1 m2) T :=
    .pat (chk := []) hp hm ht hr (by rw [(henv.pats_true hp).1]; trivial) (by simp)
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
  have HE := TypedComputationEq.proof_indices_singleton_equation (D := D) heq hs hΓ hlookup H
    howner hgen hpe hlT hrT hw hl hlarge hS hindices hzero
  have hrhs : (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2 =
      mkApps (equation.rhs.instL m1)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
    rw [hof.1]; exact happly
  rw [hrhs] at hr Hpat ⊢
  obtain ⟨_, hla, indices, major, hi, HB⟩ := singletonInstance_beta_prefix hAt hrec hru
    hgen hof hlarge hzero hlen h1 h2
  have HR := HE.symm.mkApps_fn hΓ hr
  have HC := HR.trans (TypedComputationEq.of_beta hΓ HR.defeq.hasType.2 HB)
  obtain ⟨S', E, hS', hE, W⟩ := InductiveSignature.RecursorData.propElim_wf
    henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  have Hcomp : env.IsDefEq univs Γ
      (mkApps (.const data.name m1)
        (recArgs.take data.indexOffset ++ recArgs.drop data.indexOffset ++
          [mkApps (.const ru.ctor lsC) ctorArgs]))
      (mkApps (.const data.name m1) (recArgs.take data.indexOffset ++ indices ++ [major])) T := by
    rw [hdn, List.take_append_drop]
    simpa only [mkApps_snoc] using Hpat.trans HC.defeq
  have HA := TypedComputationEq.proof_indices_spine (D := D) hΓ H hlarge hzero hw hlen
    howner hS hE W hindices
    (by simp only [List.length_take, hla]; omega)
    (by simp only [List.length_drop, hla]; omega) hi Hcomp
  rw [hdn, List.take_append_drop] at HA
  simp only [mkApps_snoc] at HA
  simpa only [mkApps_snoc] using HA.trans HC.symm

/-- Missing raw singleton coverage is confined to registered layouts whose
index telescope is not propositional. Both source and reduct typings remain
explicit. This premise alone does not solve the separate type-fork join. -/
def TypedDataIndexedSingletonPatternChainClosure (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures data S},
    OnCtx Γ (env.IsType univs) → env.pats p r →
    env.recursorRegistry p.headConst = some data → data.largeTarget = true →
    data.singletonLayout env ls = some S →
    ¬ PropTelescope env univs (data.propParams ls).reverse S.indices →
    (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero →
    p.Matches e ls captures → env.HasType univs Γ e A →
    env.HasType univs Γ (r.1.apply ls captures) A →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- Proof-indexed singleton patterns, including the empty index telescope,
are already covered. Only layouts outside that fragment remain. -/
theorem TypedDataIndexedSingletonPatternChainClosure.singleton_closure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData = env.recursorRegistry)
    (HI : TypedDataIndexedSingletonPatternChainClosure D) : TypedSingletonPatternChainClosure D := by
  intro Γ p r e A ls captures data hΓ hp hreg hl hz hm ht hr
  obtain ⟨_, _, _, _, hAt, _, _, _, _, ⟨index, howner⟩, _⟩ := recursorRegistry_entry hreg
  obtain ⟨S, hS⟩ : ∃ S, data.singletonLayout env ls = some S := by
    obtain ⟨_, _, _, _, _, hS, _, _, _, _⟩ :=
      RecursorData.singleton_shape hAt.registered hl hz howner
    exact ⟨_, hS⟩
  by_cases hprop : PropTelescope env univs (data.propParams ls).reverse S.indices
  · exact TypedComputationEq.proof_indices_singleton_pattern heq hs hregistry hΓ hp hreg hl hS hprop hz hm ht hr
  · exact HI hΓ hp hreg hl hS hprop hz hm ht hr

/-- Ordinary chain completeness now requires raw coverage only for singleton
layouts with non-propositional index telescopes. This remains conditional and
makes no strict-reduction claim for the overall strengthening problem. -/
theorem TypedComputationEq.of_defeq_of_data_indexed_singleton_closure
    (heq : env.HasCanonicalEq) (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HI : TypedDataIndexedSingletonPatternChainClosure EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A :=
  TypedComputationEq.of_defeq_of_singleton_closure heq hcon hqpat hguard
    (HI.singleton_closure heq EnvironmentCore.sound hregistry) hΓ H

end Lean4Lean.VEnv.Strengthening
