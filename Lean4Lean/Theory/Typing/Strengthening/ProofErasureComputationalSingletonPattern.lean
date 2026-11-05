import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalSingletonAlignment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDataEquation

/-! # Actual data-indexed singleton patterns from declaration certificates

Computational application typing aligns the actual independently supplied
indices with the stored equation. The equation itself uses the generic layout's
data-domain chains. No all-prefix or argument-history coverage is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params] {D : PureObservation.Definitions}

/-- Earlier declaration equalities, after adjoining the declared type formers,
must have computational chains in the ambient environment. This history
certificate has not yet been constructed by environment induction. -/
def SingletonDeclarationChains (D : PureObservation.Definitions) : Prop :=
  ∀ {data decl env₀ env₁}, RecursorRegisteredAt env data decl env₀ env₁ →
    ∀ {base E : VEnv}, base ≤ env₀ → base.addConstVals decl.typeConstants = some E →
      ∀ {A B : VExpr}, E.IsDefEqU decl.uvars [] A B → ∀ {Γ : List VExpr} {ls : List VLevel},
        OnCtx Γ (env.IsType univs) → (∀ l ∈ ls, l.WF univs) → ls.length = decl.uvars →
        TypedComputationEqU D Γ (A.instL ls) (B.instL ls)

/-- A structurally certified actual singleton pattern has a computation chain
for arbitrary dependent data indices. Type-fork joining, earlier declaration
chains and the generic layout's data-domain chains remain explicit premises. -/
theorem TypedComputationEq.computational_singleton_pattern
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hRigid : ∀ c, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hregistry : recursorData = env.recursorRegistry)
    (HN : SingletonDeclarationChains D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.pats p r)
    (hreg : env.recursorRegistry p.headConst = some data)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero)
    (HD : (∀ l ∈ m1, l.WF univs) → m1.length = data.uvars →
      ∀ S E, data.singletonLayout env m1 = some S → data.propElim m1 = some E →
      SingletonGenericDataDomainChains D S (data.propParams m1) E)
    (hm : p.Matches t m1 m2) (hJ : HasTypeC D Γ t T)
    (hr : env.HasType univs Γ (r.1.apply m1 m2) T) :
    TypedComputationEq D Γ t (r.1.apply m1 m2) T := by
  have ht := hJ.hasType
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
  have HE := TypedComputationEq.data_singleton_equation (D := D) heq hs HF hΓ hlookup H
    howner hgen hpe hlT hrT hw hl hlarge hzero (HD hw hlen)
  have hrhs : (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2 =
      mkApps (equation.rhs.instL m1)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
    rw [hof.1]; exact happly
  rw [hrhs] at hr ⊢
  have HR := HE.symm.mkApps_fn hΓ hr
  have HA := singletonInstance_alignC heq hs HF hRigid hΓ hAt hdn.symm hrec hru hgen hof
    hlarge hzero h1 h2 ht hJ HR.defeq.hasType.2 (HN hAt)
  exact (HA.at_source_type hΓ ht).trans HR.symm

end Lean4Lean.VEnv.Strengthening
