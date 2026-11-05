import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationNormal
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationUnindexedPrefix

/-! # Singleton equations from their selected prefix computations

The existing extraction construction uses only the selected recursor's prefix,
beta and syntax compatibility, followed by normal equality. Interpreting those
operations as typed chains retains the original equation assignment. In the
unindexed case prefix coverage is already unconditional.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- A trace realizes a chain at every actual source assignment in its context.
This is an interpretation interface, not an ordinary-equality completeness axiom. -/
def TypedComputationTrace (D : PureObservation.Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∀ {A}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ a A → TypedComputationEq D Γ a b A

/-- Reflexive traces preserve the supplied source typing. -/
theorem TypedComputationTrace.refl : TypedComputationTrace D Γ a a := fun _ ht => .refl ht

/-- Source replay supplies the intermediate assignment of a trace composite. -/
theorem TypedComputationTrace.trans (H : TypedComputationTrace D Γ a b)
    (H' : TypedComputationTrace D Γ b c) : TypedComputationTrace D Γ a c := by
  intro A hΓ ht
  have HC := H hΓ ht
  exact HC.trans (H' hΓ HC.defeq.hasType.2)

/-- Dependent application of traces uses the actual source function domain. -/
theorem TypedComputationTrace.app (HF : TypedComputationTrace D Γ f f')
    (HX : TypedComputationTrace D Γ x x') : TypedComputationTrace D Γ (.app f x) (.app f' x') := by
  intro A hΓ ht
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  exact (TypedComputationEq.app hΓ (HF hΓ hf) (HX hΓ hx)).at_source_type hΓ ht

/-- A fixed typed chain supplies a trace at every source assignment. -/
theorem TypedComputationTrace.of_chain (H : TypedComputationEq D Γ a b A) :
    TypedComputationTrace D Γ a b := fun hΓ ht => H.at_source_type hΓ ht

/-- Traces act on arbitrary argument spines, preserving the actual whole
application assignment even when every argument type is dependent. -/
theorem TypedComputationTrace.mkApps (H : TypedComputationTrace D Γ f g) :
    TypedComputationTrace D Γ (VExpr.mkApps f args) (VExpr.mkApps g args) := by
  induction args generalizing f g with
  | nil => exact H
  | cons a args ih => exact ih (TypedComputationTrace.app H TypedComputationTrace.refl)

/-- Applying a typed equation to a fixed spine needs only the whole source's
typing; intermediate Pi assignments are recovered by application inversion. -/
theorem TypedComputationEq.mkApps_fn
    (hΓ : OnCtx Γ (env.IsType univs)) (H : TypedComputationEq D Γ f g A)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T) :
    TypedComputationEq D Γ (VExpr.mkApps f args) (VExpr.mkApps g args) T :=
  TypedComputationTrace.mkApps (TypedComputationTrace.of_chain H) hΓ ht

/-- A typed instance of an equation can replace a proof major after its left
side beta-reduces to the same function prefix. Typing of the right instance
supplies typing of the left one; proof irrelevance aligns the two majors. This
does not require matching their constructor parameters or universe syntax. -/
theorem TypedComputationEq.apply_equation_at_proof_major
    (hΓ : OnCtx Γ (env.IsType univs)) (H : TypedComputationEq D Γ lhs rhs A)
    (ht : env.HasType univs Γ (.app f p) T)
    (hr : env.HasType univs Γ (VExpr.mkApps rhs args) T) (hp : IsProof Γ p)
    (Rβ : VExpr.BetaRed (VExpr.mkApps lhs args) (.app f q)) :
    TypedComputationEq D Γ (.app f p) (VExpr.mkApps rhs args) T := by
  have HR := H.symm.mkApps_fn hΓ hr
  have HB := TypedComputationEq.of_beta (D := D) hΓ HR.defeq.hasType.2 Rβ
  obtain ⟨_, _, hf, hpA⟩ := ht.app_inv henv hΓ
  obtain ⟨_, _, hf', hq⟩ := HB.defeq.hasType.2.app_inv henv hΓ
  have hqA := argument_at_displayed_domain hΓ hf' hf hq
  obtain ⟨P, hpP, hP⟩ := hp
  have hqP := hqA.defeqU_r henv hΓ (hpA.uniqU henv hΓ hpP)
  have HP := (TypedComputationEq.proof_irrel (D := D) hP hpP hqP).at_source_type hΓ hpA
  exact ((HP.app_arg hΓ hf).at_source_type hΓ ht).trans (HR.trans HB).symm

/-- Traces close beneath arbitrary finite lambda telescopes. The whole source
typing supplies all binder contexts and intermediate body assignments. -/
theorem TypedComputationTrace.wrapLams
    (H : TypedComputationTrace D (ds.reverse ++ Γ) a b) :
    TypedComputationTrace D Γ (VExpr.wrapLams ds a) (VExpr.wrapLams ds b) := by
  induction ds generalizing Γ with
  | nil => exact H
  | cons A ds ih =>
    intro T hΓ ht
    obtain ⟨⟨u, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ
    have H' : TypedComputationTrace D (ds.reverse ++ A :: Γ) a b := by
      intro U hc ht
      have hc' : OnCtx ((A :: ds).reverse ++ Γ) (env.IsType univs) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hc
      have ht' : env.HasType univs ((A :: ds).reverse ++ Γ) a U := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ht
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H hc' ht'
    have HB := ih H' ⟨hΓ, u, hA⟩ hb
    exact (HB.lam_body hΓ hA).at_source_type hΓ ht

/-- A beta contraction is a source-typed trace. -/
theorem TypedComputationTrace.beta :
    TypedComputationTrace D Γ (.app (.lam A b) a) (b.inst a) :=
  fun hΓ ht => .of_beta hΓ ht .beta

/-- Coverage of one selected recursor's prefixes realizes its entire stored
singleton equation as a chain, including reconstruction of dependent fields.
The normal comparison at the end uses no enriched-system confluence premise. -/
theorem TypedComputationEq.singleton_equation_of_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hlookup : recursorData data.name = some data)
    (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) (hpe : env.PatEquation equation)
    (hlT : env.HasType equation.uvars [] equation.lhs equation.type)
    (hrT : env.HasType equation.uvars [] equation.rhs equation.type)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = equation.uvars)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero)
    (hprefix : ∀ {Δ args rhs}, PrefixUnfold env univs recursorData Δ data.name levels args rhs →
      TypedComputationTrace D Δ (mkApps (.const data.name levels) args) rhs) :
    TypedComputationEq D Γ (equation.lhs.instL levels) (equation.rhs.instL levels)
      (equation.type.instL levels) := by
  obtain ⟨_, _, RL, RR, HN⟩ := H.zero_join_via_prefix heq hΓ hlookup howner hgen hpe hlT hrT
    hw hl hlarge hzero (TypedComputationTrace D) TypedComputationTrace.refl
    (fun H H' => H.trans H') (fun H H' => H.app H') (fun H => H.wrapLams)
    TypedComputationTrace.beta hprefix
  have htL : env.HasType univs Γ (equation.lhs.instL levels) (equation.type.instL levels) :=
    (hlT.instL hw).weak0 henv.ordered
  have htR : env.HasType univs Γ (equation.rhs.instL levels) (equation.type.instL levels) :=
    (hrT.instL hw).weak0 henv.ordered
  have HL := RL hΓ htL
  have HR := RR hΓ htR
  exact (HL.trans (TypedComputationEq.of_normal heq hs hΓ HL.defeq.hasType.2 HN)).trans HR.symm

/-- Every registered unindexed proposition-source singleton equation has a
typed computation chain at its stored assignment. No prefix coverage, native
recovery, checked-capture or type-fork joining hypothesis remains. -/
theorem TypedComputationEq.unindexed_singleton_equation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hlookup : recursorData data.name = some data)
    (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) (hpe : env.PatEquation equation)
    (hlT : env.HasType equation.uvars [] equation.lhs equation.type)
    (hrT : env.HasType equation.uvars [] equation.rhs equation.type)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = equation.uvars)
    (hlarge : data.largeTarget = true) (hn : data.numIndices = 0)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero) :
    TypedComputationEq D Γ (equation.lhs.instL levels) (equation.rhs.instL levels)
      (equation.type.instL levels) := by
  apply TypedComputationEq.singleton_equation_of_prefix heq hs hΓ hlookup H howner hgen hpe
    hlT hrT hw hl hlarge hzero
  intro Δ args rhs HP T hΔ ht
  cases HP with
  | intro hreg hr _ hl hw hz hg _ =>
    cases Option.some.inj (hreg.symm.trans hlookup)
    exact TypedComputationEq.generated_unindexed_prefix heq hs hΔ hlookup hr hl hz hw hn hg ht

end Lean4Lean.VEnv.Strengthening
