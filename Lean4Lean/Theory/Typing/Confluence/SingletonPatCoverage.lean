import Lean4Lean.Theory.Typing.Confluence.SingletonEquation
import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.FullChurchRosser

/-! # Coverage of a registered ι rule at a `Prop` source

A registered ι rule of a large-eliminating singleton recursor fires (`IsDefEq.pat`, check
`.true`) at instances whose major's source sort is `Prop`. The confluence engine's pattern of the
rule is guarded there (`RecursorData.guard`), and the singleton prefix unfolding computes
instead. Its coverage (`VEnv.WF.singletonPatCoverage`) chains three joins:

1. the instance `rec A (c B)` joins the β-redex of the rule's generic equation at the
   recursor's parameters, motives and minors and the major's fields
   (`VEnv.WF.singletonInstance_align`, a named stub, see below);
2. the generic equation joins at a `Prop` source by the prefix unfolding
   (`RecursorRegistered.zero_join`, ported from the verified-inductives branch), here applied to
   the equation's registered rule (`RecursorRegistered.patEquation_of_empty`);
3. the right side of the generic equation applied to those arguments is the rule's reduct.

**The stub.** Step 1 holds because the instance and the β-redex are definitionally equal: they
differ in the instance's index arguments and the major's parameters, which are definitionally
equal to the equation's by the typing of the major (injectivity of the family). Turning that
definitional equality into a join is the confluence theorem itself, at a derivation that is not
a subderivation of `IsDefEq.pat` (whose only premise is the typing of the instance). On the
verified-inductives branch the stored equation entered `IsDefEq` only through `extra` and
`appDF`, whose premises carried the index equalities as subderivations. Two routes retire it:
register the ι rules with `.defeq` alignment checks on the index and constructor-parameter holes
(`Pattern.Check.defeq`; the premises of `IsDefEq.pat` then carry the alignments, and the
induction of `IsDefEq.church_rosser` supplies their joins), or strengthen the induction to
type-joinability of rigid spines. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

section
variable [Params]
open Params

theorem FullCRDefEq.mkApps_fn (hΓ : OnCtx Γ (env.IsType univs))
    {f f' f₁ f₁' : VExpr} (hf : FullReduction Γ f f₁) (hf' : FullReduction Γ f' f₁')
    (hn : NormalEq Γ f₁ f₁') (hdef : env.IsDefEqU univs Γ f f') :
    ∀ {args : List VExpr} {T : VExpr}, env.HasType univs Γ (VExpr.mkApps f args) T →
      FullCRDefEq Γ (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  intro args
  induction args generalizing f f' f₁ f₁' with
  | nil =>
    intro T ht
    obtain ⟨_, hd⟩ := hdef
    exact ⟨⟨_, ht⟩, ⟨_, hd.hasType.2⟩, _, _, hf, hf', hn⟩
  | cons a as ih =>
    intro T ht
    obtain ⟨_, hfa⟩ := HasType.mkApps_head henv.orderedStrong hΓ (as := as) (f := .app f a) ht
    obtain ⟨A, B, hft, hat⟩ := hfa.app_inv henv.orderedStrong hΓ
    obtain ⟨C, hd⟩ := hdef
    have hf't : env.HasType univs Γ f' (.forallE A B) :=
      (hd.hasType.1.uniqU henv hΓ hft).defeqDF henv hΓ hd |>.hasType.2
    have hf₁t := hf.hasType hΓ hft
    have hf₁'t := hf'.hasType hΓ hf't
    refine ih (f := .app f a) (f' := .app f' a) (f₁ := .app f₁ a) (f₁' := .app f₁' a)
      (hf.app .rfl) (hf'.app .rfl) (.appDF hf₁t hf₁'t hat hat hn (.refl hat))
      ⟨_, .appDF ((hd.hasType.1.uniqU henv hΓ hft).defeqDF henv hΓ hd) hat⟩ ht

end

variable {env : VEnv}

/-- WAVE 4 STUB (index alignment). A typed instance of a registered ι rule of a
large-eliminating recursor at a `Prop` source joins the β-redex of the rule's generic equation
at the recursor's parameters, motives and minors and the major's fields. See the module
docstring for why this is not a consequence of the induction of `IsDefEq.church_rosser` and how
to retire it. -/
theorem WF.singletonInstance_align (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ : List VExpr} {data : RecursorData} {decl : VInductDecl} {env₀ env₁ : VEnv}
      {rec : VRecursor} {ru : VRecRule} {index : Fin data.schema.signature.constructors.size}
      {equation : VDefEq} {levels ctorLevels : List VLevel} {recArgs ctorArgs : List VExpr}
      {T : VExpr},
      OnCtx Γ (env.IsType U) →
      RecursorRegisteredAt env data decl env₀ env₁ → rec ∈ decl.recs → ru ∈ rec.rules →
      data.equation index = some equation → VRecRule.OfEquation rec ru equation →
      data.largeTarget = true →
      (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero →
      recArgs.length = rec.getMajorIdx → ctorArgs.length = ru.ctorParams + ru.nfields →
      env.HasType U Γ (VExpr.mkApps (.const rec.name levels)
        (recArgs ++ [VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs])) T →
      FullCRDefEq Γ (VExpr.mkApps (.const rec.name levels)
          (recArgs ++ [VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs]))
        (VExpr.mkApps (equation.lhs.instL levels)
          (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
            ctorArgs.drop ru.ctorParams)) := by
  sorry

/-- **Coverage of a registered ι rule at a `Prop` source of a large-eliminating recursor**: the
instance joins its reduct in the full presentation, through the β-redex of the rule's generic
equation (`WF.singletonInstance_align`) and the singleton prefix unfolding of that equation
(`RecursorRegistered.zero_join`). -/
theorem WF.singletonPatCoverage (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq) :
    letI := henv.params U
    ∀ {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 : List VLevel}
      {m2 : p.Path → VExpr} {data : RecursorData},
      OnCtx Γ (env.IsType U) → env.pats p r → env.recursorRegistry p.headConst = some data →
      data.largeTarget = true → (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero →
      p.Matches e m1 m2 → env.HasType U Γ e A →
      ∃ left right, FullReduction Γ e left ∧ FullReduction Γ (r.1.apply m1 m2) right ∧
        NormalEq Γ left right := by
  letI := henv.params U
  intro Γ p r t T m1 m2 data hΓ hp hreg hlarge hzero hm ht
  have hentry := recursorRegistry_entry hreg
  obtain ⟨decl, env₀, env₁, rec, hAt, -, hrec, hrname, hdname, -, covers⟩ := hentry
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
  have ht' : env.HasType U Γ (.app (VExpr.mkApps (.const data.name m1) recArgs)
      (VExpr.mkApps (.const ru.ctor lsC) ctorArgs)) T := by
    rw [hdn]; simpa [VExpr.mkApps_append] using ht
  obtain ⟨hw, hlen, -⟩ := RecursorRegistered.major_type henv hΓ H ht' (h1.trans hmo.symm)
  have F := RecursorData.singletonSignature H hlarge (packed := m1) hzero
  have hpe := H.patEquation_of_empty henv F.restoration hgen
  obtain ⟨hlT, hrT⟩ := H.equation_typed hgen
  have hl : m1.length = equation.uvars := hlen.trans (H.equation_uvars' hgen).symm
  have hlookup : Params.recursorData data.name = some data := by
    show env.recursorRegistry data.name = some data
    rw [hdn]; simpa [SimplePattern.iota_headConst] using hreg
  obtain ⟨L, R, hL, hR, hn⟩ := H.zero_join heq hΓ hlookup howner hgen hpe hlT hrT hw hl hlarge
    hzero
  have halign := WF.singletonInstance_align henv U hΓ hAt hrec hru hgen hof hlarge hzero h1 h2 ht
  have hXt := halign.2.1.choose_spec
  have hlΓ : env.HasType U Γ (equation.lhs.instL m1) (equation.type.instL m1) :=
    (by simpa using hlT.instL hw : env.HasType U [] _ _).weak0 henv.ordered
  have hdef : env.IsDefEqU U Γ (equation.lhs.instL m1) (equation.rhs.instL m1) := by
    have hrΓ : env.HasType U Γ (equation.rhs.instL m1) (equation.type.instL m1) :=
      (by simpa using hrT.instL hw : env.HasType U [] _ _).weak0 henv.ordered
    exact IsDefEqU.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, hL.defeq hΓ hlΓ⟩ (hn.defeq hΓ))
      ⟨_, (hR.defeq hΓ hrΓ).symm⟩
  have hj2 := FullCRDefEq.mkApps_fn hΓ hL hR hn hdef hXt
  have hrhs : (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2 =
      VExpr.mkApps (equation.rhs.instL m1)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
    rw [hof.1]; exact happly
  obtain ⟨-, -, l, r', h1', h2', h3'⟩ := FullCRDefEq.trans hΓ halign hj2
  exact ⟨l, r', h1', hrhs ▸ h2', h3'⟩

end Lean4Lean.VEnv
