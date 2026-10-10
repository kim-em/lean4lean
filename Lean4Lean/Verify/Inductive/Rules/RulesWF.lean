import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped

/-! # `rules_wf` from the generated equations

The rule clause of `VInductDecl.WF` (`rules_wf`) types each model rule of the installed
recursors as a schematic ι rule (`VEnv.PatTyped`). On the source branch the rules were stored
equations and their typing was the `VDefEq.WF` of the generated equations; here the rule is a
pattern and its typing is restated from that `VDefEq.WF` (PORT_PLAN section 2.3,
`InductiveSignature.Instance.equation_patTyped`). This file identifies each model rule with
its generated equation through the kernel recursor it translates (`TrRecursor`, functional by
`TrExprS.unique`) and the generator's coverage of the kernel rules (`TrRecursorRule`), and
reads the counts off the recursor metadata (`RecursorMetadata`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Transport of a typed ι rule along equalities of its data. -/
theorem VEnv.patTyped_iota_congr {env : VEnv} {r r' c c' : Name}
    {np np' nm nm' nmin nmin' nind nind' cnp cnp' nf nf' : Nat} {rhs rhs' : VExpr}
    {hc : rhs.Closed} {hc' : rhs'.Closed}
    (hr : r = r') (hcn : c = c') (hnp : np = np') (hnm : nm = nm') (hnmin : nmin = nmin')
    (hnind : nind = nind') (hcnp : cnp = cnp') (hnf : nf = nf') (hrhs : rhs = rhs')
    (H : env.PatTyped (SimplePattern.iota r (np+nm+nmin+nind) c (cnp+nf)).toPattern
      (SimplePattern.iotaRHS r c np nm nmin nind cnp nf rhs hc, .true)) :
    env.PatTyped (SimplePattern.iota r' (np'+nm'+nmin'+nind') c' (cnp'+nf')).toPattern
      (SimplePattern.iotaRHS r' c' np' nm' nmin' nind' cnp' nf' rhs' hc', .true) := by
  subst hr hcn hnp hnm hnmin hnind hcnp hnf hrhs; exact H

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The rule coverage of a recursor check (the `trRules` clause of `RuleTranslations`): each
kernel recursor's rules are, in order, the generated equations of the constructors it owns. -/
def RecursorCheck.RulesCovered (H : RecursorCheck R outEnv) : Prop :=
  List.Forall₂ (fun (owner : Fin H.signature.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule H.generation H.outVEnv rval.levelParams)
        (H.signature.ownedConstructors owner) rval.rules)
    (List.finRange H.signature.families.size) H.rvals

/-- The generated equations are well formed in the recursor stage (the `equationsWF` clause
of `RuleTranslations`). -/
def RecursorCheck.EquationsWF (H : RecursorCheck R outEnv) : Prop :=
  ∀ df ∈ H.generation.equations, df.WF H.outVEnv

/-- Every model rule fires on a constructor with the signature's parameter count: the
constructor parameter count `TrRecursor` reads off the output map is the declaration's. -/
def RecursorCheck.RuleCtorParams (H : RecursorCheck R outEnv) : Prop :=
  ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ru.ctorParams = H.signature.params.length

/-- A model rule of a recursor check is, reduct for reduct, the generated equation of a
constructor owned by its recursor's family, with the generated counts. -/
theorem RecursorCheck.rule_equation (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hparams : H.RuleCtorParams) {r : VRecursor} (hr : r ∈ H.recs) {ru : VRecRule}
    (hru : ru ∈ r.rules) :
    ∃ index : Fin H.signature.constructors.size,
      r.name = H.generation.recursorName H.signature.constructors[index].owner ∧
      r.numParams = H.signature.params.length ∧
      r.numMotives = H.signature.families.size ∧
      r.numMinors = H.signature.constructors.size ∧
      r.numIndices = H.signature.constructors[index].indices.length ∧
      ru.ctor = H.signature.constructors[index].name ∧
      ru.ctorParams = H.signature.params.length ∧
      ru.nfields = H.signature.constructors[index].fields.length ∧
      ru.rhs = (H.generation.equation index).rhs := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hlenR : H.recs.length = H.rvals.length := H.recs_length
  have hlenC : (List.finRange H.signature.families.size).length = H.rvals.length :=
    List.Forall₂.length_eq hcov
  have hiR : i < H.rvals.length := hlenR ▸ hi
  have hiF : i < H.signature.families.size := by
    have := hlenC; simp only [List.length_finRange] at this; omega
  have Htr := List.forall₂_getElem H.trRecs i hiR hi
  have Hmeta := List.forall₂_getElem H.metadata i (by simpa using hiF) hiR
  have Hcov := List.forall₂_getElem hcov i (by simpa using hiF) hiR
  simp only [List.getElem_finRange, Fin.cast_mk] at Hmeta Hcov
  -- the model recursor is the generated recursor of family `i`
  have hrec : H.recs[i].toVConstVal = H.generation.recursor ⟨i, hiF⟩ := by
    have h := congrArg (·[i]?) H.recursors_eq
    simpa [List.getElem?_eq_getElem hi, InductiveSignature.Instance.recursors, hiF] using h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hru
  have hjK : j < H.rvals[i].rules.length := (List.Forall₂.length_eq Htr.rules) ▸ hj
  have Hrule := List.forall₂_getElem Htr.rules j hjK hj
  obtain ⟨hctor, hnf, -, hrhs⟩ := Hrule
  have hjO : j < (H.signature.ownedConstructors ⟨i, hiF⟩).length := (List.Forall₂.length_eq Hcov) ▸ hjK
  have Hgen := List.forall₂_getElem Hcov j hjO hjK
  obtain ⟨index, hindex⟩ : ∃ index, (H.signature.ownedConstructors ⟨i, hiF⟩)[j] = index :=
    ⟨_, rfl⟩
  rw [hindex] at Hgen
  have hown : H.signature.constructors[index].owner = ⟨i, hiF⟩ := by
    have hmem : index ∈ H.signature.ownedConstructors ⟨i, hiF⟩ := hindex ▸ List.getElem_mem _
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
    exact hmem.2
  have harity := H.models.constructorArity _ (Array.getElem_mem_toList (i := index.val) index.isLt)
  refine ⟨index, ?_, ?_, ?_, ?_, ?_, ?_, hparams _ hr _ hru, ?_, ?_⟩
  · rw [hown]; have := congrArg VConstVal.name hrec; simpa [InductiveSignature.Instance.recursor]
  · rw [Htr.numParams]; exact Hmeta.numParams
  · rw [Htr.numMotives]; exact Hmeta.numMotives
  · rw [Htr.numMinors]; exact Hmeta.numMinors
  · rw [Htr.numIndices, Hmeta.numIndices]
    have hfam := congrArg (fun o : Fin H.signature.families.size =>
      H.signature.families[o].indices.length) hown
    exact (harity.trans hfam).symm
  · rw [hctor]; exact Hgen.ctor
  · rw [hnf]; exact Hgen.nfields
  · exact (TrExprS.unique Hgen.rhs hrhs).symm

/-- `VInductDecl.WF.rules_wf` of a recursor check, from the rule coverage, the
well-formedness of the generated equations and the constructor parameter counts. -/
theorem RecursorCheck.rules_wf_of (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hwf : H.EquationsWF) (hparams : H.RuleCtorParams) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      H.outVEnv.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor
          r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
          .true) := by
  intro r hr ru hru hc
  obtain ⟨index, hname, hnp, hnm, hnmin, hnind, hctor, hcnp, hnf, hrhs⟩ :=
    H.rule_equation hcov hparams hr hru
  have hc' : (H.generation.equation index).rhs.Closed := hrhs ▸ hc
  have hdf := hwf _ (List.mem_map.2 ⟨index, List.mem_finRange _, rfl⟩)
  exact VEnv.patTyped_iota_congr hname.symm hctor.symm hnp.symm hnm.symm hnmin.symm
    hnind.symm hcnp.symm hnf.symm hrhs.symm
    (H.generation.equation_patTyped H.outVEnv_wf index hdf hc')

end
end VerifyInductive
end Lean4Lean
