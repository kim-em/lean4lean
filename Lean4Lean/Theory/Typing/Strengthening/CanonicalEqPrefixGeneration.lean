import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqPrefixMetadata
import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout

/-! # The actual canonical Eq prefix program

The generated program retains the canonical equation and its four captures.
Its residual output is the manual K-prefix lambda, as a syntactic equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature

/-- The exact open equation body extracted from the canonical iota equation. -/
def canonicalEqRecBody : RecursorSchema.EquationBody where
  domains := [.sort (.param 1), .bvar 0, canonicalEqRecMotive, canonicalEqRecMinor]
  lhs := canonicalEqRecRule.lhs.lamBody
  rhs := .bvar 0
  type := canonicalEqRecRule.type.forallResult

/-- Extraction of the installed canonical equation succeeds literally. -/
theorem canonicalEqRecBody_extract : RecursorSchema.EquationBody.extract
    canonicalEqRecRule.lhs canonicalEqRecRule.rhs canonicalEqRecRule.type =
    some canonicalEqRecBody := rfl

/-- The canonical prefix before its major, with its generated constructor left
explicit until the reconstruction metadata has been identified. -/
def canonicalEqPrefixProgram (v w : VLevel) (α a M m b ctor : VExpr) :
    RecursorData.PrefixUnfolding where
  domains := [eqApp w α a b]
  result := .app (.app M.lift b.lift) (.bvar 0)
  constructor := ctor
  equation := canonicalEqRecRule
  equationBody := canonicalEqRecBody
  captures := [α.lift, a.lift, M.lift, m.lift]
  levels := [v, w]

/-- Its exact output is the K-prefix lambda; the reconstructed proof does not
occur in the four-capture equation RHS. -/
theorem canonicalEqPrefixProgram_rhs :
    (canonicalEqPrefixProgram v w α a M m b ctor).rhs = .lam (eqApp w α a b) m.lift := rfl

/-- The actual Prop eliminator reconstructs the canonical Eq.refl constant. -/
theorem eqRec_propElim_ctor (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v, w] ≈ .zero)
    {S : SingletonLayout} {E : PropElim}
    (hS : data.singletonLayout env [v, w] = some S) (hE : data.propElim [v, w] = some E) :
    E.ctor = .const ``Eq.refl [w] := by
  obtain ⟨hfam, hcs, hp, _, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  have hu := (hr.eqRec_target heq hn).1
  have hlen : [v, w].length = data.uvars := by simp [hu]
  have hfields := hr.eqRec_fields_empty heq hn hz hlen hS hE
  let i : Fin data.schema.signature.constructors.size := ⟨0, by omega⟩
  have ho : data.schema.signature.constructors[i].owner = data.owner := by
    apply Fin.ext
    have := data.owner.isLt
    have := data.schema.signature.constructors[i].owner.isLt
    omega
  obtain ⟨D, lb, rb, tb, X, he, he', hex, _, _, hleft, _⟩ :=
    RecursorData.singleton_equation_syntax hr (hr.eqRec_large heq hn) hz hlen ho hS hE
  have heqrule := Option.some.inj (hseq.symm.trans (he'.trans he))
  have hex' : RecursorSchema.EquationBody.extract canonicalEqRecRule.lhs
      canonicalEqRecRule.rhs canonicalEqRecRule.type = some ⟨D, lb, rb, tb⟩ := by
    rw [heqrule]; exact hex
  have hbody := Option.some.inj (canonicalEqRecBody_extract.symm.trans hex')
  have hlb : canonicalEqRecBody.lhs = lb := congrArg RecursorSchema.EquationBody.lhs hbody
  have hplen := (RecursorData.singletonLayout_lengths hS).2.trans hp
  rw [← hlb] at hleft
  have hlast := congrArg (fun e => match e with | .app _ a => a | _ => e) hleft
  have hlast' : VExpr.app (.app (.const ``Eq.refl [w]) (.bvar 3)) (.bvar 2) =
      VExpr.app (.app E.ctor (.bvar 3)) (.bvar 2) := by
    simpa [canonicalEqRecBody, canonicalEqRecRule, lamBody, instL, VLevel.inst,
      hplen, hfields, vars, mkApps, List.range, List.range.loop] using hlast
  exact (VExpr.app.inj (VExpr.app.inj hlast').1).1.symm

/-- Supplying the five visible arguments to the stored type leaves exactly
the equality-proof domain and the motive applied to that proof. -/
theorem canonicalEqRec_supply_five : RecursorData.supplyType [α, a, M, m, b]
    (canonicalEqRecType.instL [v, w]) =
    some (.forallE (eqApp w α a b) (.app (.app M.lift b.lift) (.bvar 0))) := by
  simp [RecursorData.supplyType, canonicalEqRecType, canonicalEqRecMotive,
    canonicalEqRecMinor, instL, VLevel.inst, inst, instVar, inst_liftN_lo, eqApp, lift]

/-- The real singleton generator returns the explicit canonical K-prefix
program. No endpoint conversion is needed for generation itself. -/
theorem eqRec_prefix_generated (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v, w] ≈ .zero)
    {S : SingletonLayout} {E : PropElim}
    (hS : data.singletonLayout env [v, w] = some S) (hE : data.propElim [v, w] = some E) :
    data.singletonUnfolding env U [v, w] [α, a, M, m, b] =
      some (canonicalEqPrefixProgram v w α a M m b (eqReflApp w α.lift a.lift)) := by
  obtain ⟨hu, hoff, _, _⟩ := hr.eqRec_target heq hn
  obtain ⟨hfam, hcs, hp, _, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  have hlen : [v, w].length = data.uvars := by simp [hu]
  have hfields := hr.eqRec_fields_empty heq hn hz hlen hS hE
  have hctor := eqRec_propElim_ctor heq hr hn hz hS hE
  have hio : data.indexOffset = 4 := by
    simp [RecursorData.indexOffset, hp, hfam, hcs]
  obtain ⟨ty, hty⟩ := hr.recursorType_exists
  have hc := hr.recursorType hty
  rw [hn, heq.2.2.1] at hc
  have htype := congrArg VConstant.type (Option.some.inj hc)
  change canonicalEqRecType = ty at htype
  rw [← htype] at hty
  simp only [RecursorData.singletonUnfolding, hu, hoff, hty,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    bne_self_eq_false, Nat.lt_irrefl, decide_false, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte]
  simp [RecursorData.singletonReconstruction, hS, hE, hfields, hctor,
    hp, hio, hseq, canonicalEqRecBody_extract, canonicalEqRec_supply_five, takeForalls, PropElim.occ,
    vars, canonicalEqPrefixProgram, canonicalEqRecBody, eqReflApp, mkApps, lift]

end Lean4Lean.VEnv.Strengthening
