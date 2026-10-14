import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary
import Lean4Lean.Theory.Typing.Strengthening.EqRecBeforeMajorReplay
import Lean4Lean.Theory.Inductive.CanonicalEqSignature

/-! # Reading canonical Eq prefix metadata from the installed recursor

The registry entry is arbitrary: its universe and telescope facts are recovered
from the installed canonical type, rather than assumed as extra metadata.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv}

/-- The installed type fixes the target universe and motive position of every
registered canonical equality recursor. -/
theorem RecursorRegistered.eqRec_target (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec) :
    data.uvars = 2 ∧ data.majorOffset = 5 ∧
      data.numParams + data.owner.val = 2 ∧ data.target = .param 0 := by
  obtain ⟨type, ht⟩ := hr.recursorType_exists
  have hc := hr.recursorType ht
  rw [hn, heq.2.2.1] at hc
  have hu := congrArg VConstant.uvars (Option.some.inj hc)
  have htype := congrArg VConstant.type (Option.some.inj hc)
  change canonicalEqRecType = type at htype
  obtain ⟨ci, hci, harity⟩ := hr.constant_piArity
  rw [hn, heq.2.2.1] at hci
  cases Option.some.inj hci
  change 6 = data.majorOffset + 1 at harity
  have hoff : data.majorOffset = 5 := by omega
  have hi := hr.eqRec_numIndices heq hn
  obtain ⟨domains, mds, hs, hlen, hm, hmlen⟩ := RecursorData.recursorType_shape ht
  have hresult := congrArg VExpr.forallResult hs
  rw [VExpr.forallResult_wrapForalls, ← htype] at hresult
  simp [hi, vars, mkApps, canonicalEqRecType, forallResult] at hresult
  have howner := data.owner.isLt
  have hpos : data.numParams + data.owner.val = 2 := by
    simp only [RecursorData.majorOffset, RecursorData.indexOffset] at hoff
    omega
  have hscan := takeForalls_wrapForalls domains (mkApps
    (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
      (data.schema.signature.families.size - 1 - data.owner.val)))
    (vars data.numIndices 1 ++ [.bvar 0]))
  rw [← hs, ← htype, hlen, hoff] at hscan
  have hds := congrArg Prod.fst (Option.some.inj hscan)
  dsimp only [Prod.fst] at hds
  rw [hpos, ← hds] at hm
  have hend := congrArg VExpr.forallResult (Option.some.inj hm)
  rw [VExpr.forallResult_wrapForalls] at hend
  change sort (.param 0) = sort data.target at hend
  exact ⟨hu.symm, hoff, hpos, (VExpr.sort.inj hend).symm⟩

/-- Canonical Eq's registered target is genuinely large at generic universes. -/
theorem RecursorRegistered.eqRec_large (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec) :
    data.largeTarget = true := by
  obtain ⟨hu, _, _, ht⟩ := hr.eqRec_target heq hn
  simp [RecursorData.largeTarget, ht, hu, VLevel.eval]

/-- Any typed five-argument Eq.rec occurrence forces its registered source
universe to Prop. The final major is supplied by a fresh equality-proof binder. -/
theorem RecursorRegistered.eqRec_source_zero (henv : env.WF) (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType U))
    (ht : VExpr.WF env U Γ (Strengthening.eqRecBeforeMajor v w α a M m b)) :
    data.sourceLevel [v, w] ≈ .zero := by
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := Strengthening.eqRecBeforeMajor_typings henv heq hΓ ht
  have hf := Strengthening.eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  have hE := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType U) := ⟨hΓ, _, hE⟩
  have hbody : env.HasType U (eqApp w α a b :: Γ)
      (.app (Strengthening.eqRecBeforeMajor v w α a M m b).lift (.bvar 0))
      (.app (.app M.lift b.lift) (.bvar 0)) := by
    simpa [lift, liftN, inst, instVar, inst_liftN_lo, inst_lift, liftN_liftN,
      inst_liftN_bvar] using HasType.app (hf.weak henv.ordered) (.bvar .zero)
  have hbody' : env.HasType U (eqApp w α a b :: Γ)
      (.app (mkApps (.const data.name [v, w]) [α.lift, a.lift, M.lift, m.lift, b.lift]) (.bvar 0))
      (.app (.app M.lift b.lift) (.bvar 0)) := by
    simpa [Strengthening.eqRecBeforeMajor, hn, mkApps, lift, liftN] using hbody
  apply Classical.byContradiction
  intro hnot
  exact hr.major_not_proof henv hΓE hbody'
    (by simpa using (hr.eqRec_target heq hn).2.1.symm) hnot
    (HasType.bvar Lookup.zero) (hE.weak henv.ordered)

/-- At a Prop-source occurrence, the actual registered singleton equation is
exactly the canonical Eq iota equation. This also fixes both signature sizes,
the two parameters, and identity restoration. -/
theorem RecursorRegistered.eqRec_singleton_equation (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel packed ≈ .zero) :
    data.schema.signature.families.size = 1 ∧
      data.schema.signature.constructors.size = 1 ∧ data.numParams = 2 ∧
      data.schema.restoration = {} ∧ data.singletonEquation = some canonicalEqRecRule := by
  obtain ⟨hu, hoff, hpos, _⟩ := hr.eqRec_target heq hn
  have F := RecursorData.singletonSignature hr (hr.eqRec_large heq hn) hz
  have hfam := F.families
  have hov : data.owner.val = 0 := by have := data.owner.isLt; omega
  have hp : data.numParams = 2 := by omega
  have hi := hr.eqRec_numIndices heq hn
  have hcs : data.schema.signature.constructors.size = 1 := by
    simp only [RecursorData.majorOffset, RecursorData.indexOffset, hp, hi, F.families] at hoff
    omega
  let i : Fin data.schema.signature.constructors.size := ⟨0, by omega⟩
  have ho : data.schema.signature.constructors[i].owner = data.owner := by
    apply Fin.ext
    have := data.schema.signature.constructors[i].owner.isLt
    simp only [hov]
    omega
  have hfr : List.finRange data.schema.signature.constructors.size = [i] := by
    apply List.ext_getElem (by simp [hcs])
    intro n h1 h2
    simp only [List.length_finRange, hcs] at h1
    simp only [List.getElem_finRange, List.getElem_singleton]
    ext; simp [i]; omega
  have howner : data.owner = ⟨0, by rw [F.families]; omega⟩ := Fin.ext hov
  have hname : data.recursorInstance.recursorName ⟨0, by rw [F.families]; omega⟩ = ``Eq.rec := by
    simpa [RecursorData.name, F.restoration, Restoration.recursorName, howner,
      RecursorData.recursorInstance] using hn
  have hc := F.recursor
  rw [hn, heq.2.2.1] at hc
  have htype := congrArg VConstant.type (Option.some.inj hc)
  have heqs := data.recursorInstance.eqRecEquations F.families hcs hp hu hname
    (by simpa only [howner] using htype.symm)
  simp only [Instance.equations, hfr, List.map_cons, List.map_nil, List.cons.injEq] at heqs
  refine ⟨F.families, hcs, hp, F.restoration, ?_⟩
  simp only [RecursorData.singletonEquation, hfr]
  rw [List.filter_cons_of_pos
    (p := fun j : Fin data.schema.signature.constructors.size =>
      data.schema.signature.constructors[j].owner == data.owner)
    (by simpa using ho), List.filter_nil]
  simp [heqs.1, F.restoration]


/-- The generated layout of canonical Eq has no fields. This follows from the
actual equation's four captures, rather than an assumed constructor layout. -/
theorem RecursorRegistered.eqRec_fields_empty (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel packed ≈ .zero) (hlen : packed.length = data.uvars)
    {S : SingletonLayout} {E : PropElim}
    (hS : data.singletonLayout env packed = some S) (hE : data.propElim packed = some E) :
    S.fields = [] := by
  obtain ⟨hfam, hcs, hp, _, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  let i : Fin data.schema.signature.constructors.size := ⟨0, by omega⟩
  have ho : data.schema.signature.constructors[i].owner = data.owner := by
    apply Fin.ext
    have := data.owner.isLt
    have := data.schema.signature.constructors[i].owner.isLt
    omega
  obtain ⟨D, lb, rb, tb, X, he, he', hex, hD, hX, _⟩ :=
    RecursorData.singleton_equation_syntax hr (hr.eqRec_large heq hn) hz hlen ho hS hE
  have heqrule := Option.some.inj (hseq.symm.trans (he'.trans he))
  have hex' : RecursorSchema.EquationBody.extract canonicalEqRecRule.lhs
      canonicalEqRecRule.rhs canonicalEqRecRule.type = some ⟨D, lb, rb, tb⟩ := by
    rw [heqrule]; exact hex
  have hdlen := congrArg (fun ob => ob.map (fun body => body.domains.length)) hex'
  change some 4 = some D.length at hdlen
  have h4 := Option.some.inj hdlen
  have hplen := (RecursorData.singletonLayout_lengths hS).2
  have hl := congrArg List.length hD
  simp only [List.length_map, List.length_append, insertBinders, List.length_zipIdx] at hl
  apply List.length_eq_zero_iff.mp
  omega

end Lean4Lean.VEnv
