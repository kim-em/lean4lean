import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqPrefixGeneration
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent

/-! # The literal family propositions of the canonical equality prefix

Read the extraction family and constructor index from the registered recursor
and canonical iota equation. Empty reconstruction fields then leave the
reflexive equality family literally, before any certificate interpretation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim

/-- The actual extraction family has exactly the universe arguments of Eq.refl
and the family name fixed by the installed Eq.rec type. -/
theorem eqRec_propElim_family (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E) :
    E.family = .const ``Eq [w] := by
  have hctor := eqRec_propElim_ctor heq hr hn hz hS hE
  obtain ⟨_, _, _, hrest, _⟩ := hr.eqRec_singleton_equation heq hn hz
  have hname := hr.eqRec_family heq hn
  simp [ClosedStructure.family, hrest, Restoration.headName, Restoration.recursorName] at hname
  unfold RecursorData.propElim at hE
  simp only [bind, Option.bind_eq_some_iff] at hE
  obtain ⟨k, _, i, _, hE⟩ := hE
  cases Option.some.inj hE
  have hls := (VExpr.const.inj hctor).2
  change VExpr.const _ _ = _
  simp only [VExpr.const.injEq]
  exact ⟨by simpa only [Fin.getElem_fin] using hname, hls⟩

/-- The unique reconstructed index in the canonical prefix is its second
parameter, read literally from the installed iota spine. -/
theorem eqRec_propElim_indices (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E) :
    E.ctorIndices = [.bvar 0] := by
  obtain ⟨hfam, hcs, hp, _, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  have hu := (hr.eqRec_target heq hn).1
  have hlen : [v,w].length = data.uvars := by simp [hu]
  have hfields := hr.eqRec_fields_empty heq hn hz hlen hS hE
  have hio : data.indexOffset = 4 := by
    simp [RecursorData.indexOffset, hp, hfam, hcs]
  let i : Fin data.schema.signature.constructors.size := ⟨0, by omega⟩
  have ho : data.schema.signature.constructors[i].owner = data.owner := by
    apply Fin.ext
    have := data.owner.isLt
    have := data.schema.signature.constructors[i].owner.isLt
    omega
  obtain ⟨D, lb, rb, tb, X, he, he', hex, _, _, hleft, _⟩ :=
    RecursorData.singleton_equation_syntax hr (hr.eqRec_large heq hn) hz hlen ho hS hE
  have heqrule := Option.some.inj (hseq.symm.trans (he'.trans he))
  have hex' : RecursorSchema.EquationBody.extract
      canonicalEqRecRule.lhs canonicalEqRecRule.rhs canonicalEqRecRule.type =
      some ⟨D, lb, rb, tb⟩ := by
    rw [heqrule]
    exact hex
  have hbody := Option.some.inj (canonicalEqRecBody_extract.symm.trans hex')
  have hlb : canonicalEqRecBody.lhs = lb := congrArg RecursorSchema.EquationBody.lhs hbody
  rw [← hlb] at hleft
  have he : mkApps (.const ``Eq.rec [v,w]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2] =
      mkApps (.const ``Eq.rec [v,w]) (vars 4 0 ++ E.ctorIndices.map (·.liftN 2 0)) := by
    simpa [canonicalEqRecBody, canonicalEqRecRule, lamBody, instL, VLevel.inst,
      hn, hio, hfields, mkApps] using (VExpr.app.inj hleft).1
  have hargs := (mkApps_const_inj he).2.2
  simp [vars, List.range, List.range.loop] at hargs
  apply (List.map_inj_right (f := fun e : VExpr => e.liftN 2 0)
    (fun _ _ H => VExpr.liftN_inj.mp H)).mp
  simpa [VExpr.liftN, liftVar] using hargs.symm

/-- With its two parameters supplied, the actual reconstructed family is
literally reflexive equality, independently of the requested index and major. -/
theorem eqRec_transportedFamily (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E) :
    transportedFamily S (data.propParams [v,w]) E [α,a] idx major = eqApp w α a a := by
  have hu := (hr.eqRec_target heq hn).1
  have hp := (hr.eqRec_singleton_equation heq hn hz).2.2.1
  have hfields := hr.eqRec_fields_empty heq hn hz (by simp [hu]) hS hE
  have hfamily := eqRec_propElim_family heq hr hn hz hS hE
  have hindices := eqRec_propElim_indices heq hr hn hz hS hE
  have hplen := (RecursorData.singletonLayout_lengths hS).2.trans hp
  simp [transportedFamily, branchFamily, branchPa, hfields, hfamily, hindices,
    hplen, transportedFields, transportedWitnesses, SingletonLayout.substHat, bvarRange, List.range, List.range.loop, instOuter_cons, instOuter_nil,
    VExpr.inst, instVar, VExpr.inst_lift, eqApp, mkApps]

/-- The canonical five-argument family guard compares reflexive Eq with the
requested Eq under the single fresh proof major. This is literal syntax for
any comparison relation, not a semantic implication or completeness claim. -/
theorem eqRec_family_guard_iff (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E) :
    GuardedSingleton.FamilyGuard Cmp Γ data [v,w] [α,a,M,m,b]
      (canonicalEqPrefixProgram v w α a M m b reconstructed) S E ↔
      Cmp (eqApp w α a b :: Γ) (eqApp w α.lift a.lift a.lift)
        (eqApp w α.lift a.lift b.lift) := by
  obtain ⟨hfam, hcs, hp, _, _⟩ := hr.eqRec_singleton_equation heq hn hz
  have hoff := (hr.eqRec_target heq hn).2.1
  have hi := hr.eqRec_numIndices heq hn
  have hio : data.indexOffset = 4 := by
    simp [RecursorData.indexOffset, hp, hfam, hcs]
  simp only [GuardedSingleton.FamilyGuard, RecursorData.openedArguments,
    canonicalEqPrefixProgram, hoff, hp, hio, hi, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.reverse_cons, List.reverse_nil, List.singleton_append]
  rw [eqRec_transportedFamily heq hr hn hz hS hE, eqRec_propElim_family heq hr hn hz hS hE]
  rfl

end Lean4Lean.VEnv.Strengthening
