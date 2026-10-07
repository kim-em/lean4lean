import Lean4Lean.Theory.Typing.ShapeModel.RuleValidGenericSyntax
import Lean4Lean.Theory.Typing.ShapeModel.EnvSchemaTypes

/-!
# Validity of generic eliminator equations

At an eliminator registration of the history, every instance of a generic equation of the new
schema permitted by `Permission` is valid in the shape model of the final environment
(`generic_elimOK`). The major is a source constructor or a container constructor; mode C (a
proposition major) only arises when the target universe is zero, since the permission excludes
large elimination from a possible proposition.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem genericLevels_inst {schema : CaseSchema} {levels : List VLevel}
    (h : levels.length = schema.signature.uvars) (target : VLevel) :
    schema.genericLevels.map (·.inst (target :: levels)) = levels := by
  apply List.ext_getElem (by simp [CaseSchema.genericLevels, h])
  intro i h1 h2
  simp [CaseSchema.genericLevels, VLevel.inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem generic_elimOK {E base : VEnv} {T : Tables} {source : VInductDecl}
    {block : VInductBlock} {schema : CaseSchema} {key : Name}
    (H : env.WF) (hgood : Good env E) (hEW : E.WF) (hle : E.addEliminator key schema ≤ env)
    (hbase : base.WF) (hbl : base ≤ E) (hcert : schema.Certified base source block)
    (hkey : source.types.head?.map (·.name) = some key)
    (hconsts : (∀ value ∈ block.types ++ block.ctors,
      E.constants value.name = some value.toVConstant) ∧ E.defeqs = base.defeqs ∧
      schema.ProjNamesRegistered E key)
    (hfresh : schema.Fresh E key) (hcompat : schema.StructCompat E) (hT : T.Inv E)
    (hext : (T.addSchema E source).Extends (envTables env))
    (hfam : ∀ I d, (T.addSchema E source).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    (hfrz : ∀ c, SchemaCtorReserved (E.addEliminator key schema) c →
      (T.addSchema E source).fam c = none → (envTables env).fam c = none) :
    letI := envSig env; ElimOK env key schema := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  intro owner rules df U levels target Γ typeLevel hgen hdf hRC hperm hTy hL hR
  have hreg : env.eliminators key schema := hle.eliminators VEnv.addEliminator_self
  obtain ⟨Th0, hT0, -⟩ := ShapeModel.CaseSchema.Certified.genericType_closed hcert hbase owner
  have hcert' := hcert
  obtain ⟨expanded, g0, aux, hdata, hprior, hr, hnames⟩ := hcert'
  obtain ⟨nf, Cv, Ds, idx, mR, Es, doms₀, TbH, c, lv, ps, Fn, lvF, pargs, hl, hrr, ht, hDs,
    hidx, hmot, hEs, hThs, hdoms, hpl, hslot⟩ :=
    generic_syntax hdata hprior hr hnames hgen hdf hT0
  have hlen := hperm.length
  have hG : schema.genericLevels.length = schema.signature.uvars := by
    simp [CaseSchema.genericLevels]
  have hSM : SchemaMajor env c := ⟨key, schema, hreg, owner, rules, df, _, lv, _, hgen, hdf, by
    rw [hl, stripLams_wrapLams', mkApps_snoc]; rfl⟩
  obtain ⟨ci, d, hci, hfamd, hsem, hstr, hkuv, ⟨dF, hdF⟩, L, nL, hsemL, hlevel⟩ :=
    generic_slot_sem H hgood hEW hle hbase hbl hdata hprior hr hnames hconsts.1 hconsts.2.1 hT
      hext hfam hfrz owner hG (hslot.imp (fun ⟨F, hF, hFo, h1, _, h3, h4⟩ => ⟨F, hF, hFo, h1, h3, h4⟩)
        (fun ⟨a, ha, h0, h1, h2, _, h4, h5⟩ => ⟨a, ha, h0, h1, h2, h4, h5⟩)) hSM
  obtain ⟨hncF, hnrF⟩ := fam_facts H hdF
  -- the rule
  have hnfS : schemaNf df = nf := schemaNf_eq (by intros; simp) hl hrr
  have hrule : EnvRule env (majorRule (structNp env) (.elim key owner.val) schema.genericUvars df
      nf) := hnfS ▸ .inr (.inr (.inr ⟨key, schema, hreg, owner, rules, df, hgen, hdf, rfl⟩))
  have heq := majorRule_eq (np := structNp env) (h := .elim key owner.val)
    (u := schema.genericUvars) (hd := .elim key owner.val (.param 0 :: schema.genericLevels))
    rfl (by intros; simp) hl hrr
  have hRcl0 : (VExpr.mkApps (.bvar mR) (vars nf 0)).ClosedN Ds.length := by
    have := closedN_of_wrapLams (k := 0) (hrr ▸ hRC.2.1)
    simpa using this
  -- instantiation
  have hls : (VLevel.param 0 :: schema.genericLevels).map (·.inst (target :: levels)) =
      target :: levels := by
    simp only [List.map_cons]
    rw [genericLevels_inst hlen]; rfl
  have hhd : (VExpr.elim key owner.val (.param 0 :: schema.genericLevels)).instL (target :: levels) =
      Head.toExpr (.elim key owner.val) (target :: levels) := by
    simp only [VExpr.instL, Head.toExpr, hls]
  rw [hl, ruleLhs_instL, ht, ruleType_instL, hhd] at hL
  rw [hrr, wrapLams_instL', ht, ruleType_instL] at hR
  rw [hl, ruleLhs_instL, hrr, wrapLams_instL', hhd]
  obtain ⟨hm, hmot'⟩ := hmot
  refine rule_instance_valid H hrule (by rw [heq]) (by rw [heq]; simp [CaseSchema.genericUvars, hlen])
    (npre := schema.signature.params.length + (1 + Cv))
    (by rw [heq]; exact hDs) (by rw [heq]) (by rw [heq]) (by rw [heq])
    (by rw [heq, hDs, Nat.add_sub_cancel]) (by simp [hDs])
    (by rw [← hDs]; exact hRcl0.instL) hL hR (Th := Th0.instL (target :: levels))
    ⟨Th0, sig_elimType H hreg hT0, rfl⟩
    (TbH := TbH.instL (target :: levels)) (doms₀ := doms₀.map (·.instL (target :: levels)))
    (F := Fn) (lvF := lvF.map (·.inst (target :: levels)))
    (pargs := pargs.map (·.instL (target :: levels))) ?_ (by simp [hdoms, hidx]) (by simp [hpl])
    hncF hnrF hci hfamd hsem hstr (fun _ => .rfl) ?_ (iM := schema.signature.params.length)
    (by simp; omega) ?_ (Es := Es.map (·.instL (target :: levels)))
    (tgt := (VLevel.param 0).inst (target :: levels)) (by simp [hEs, hidx]) ?_
  · rw [hThs, wrapForalls_instL']
    simp only [List.map_append, List.map_cons, List.map_nil, VExpr.instL_mkApps, vars_instL, hidx]
    rfl
  · simp only [List.length_map, hDs]
    congr 2
    omega
  · simp only [List.getElem_map, hmot', wrapForalls_instL']
    rfl
  · intro hfp
    rcases hperm.admissible with hnz | htz
    · exfalso
      have hnz' : ((schema.signature.families[owner].resultLevel.inst schema.genericLevels).inst
          (target :: levels)).IsNeverZero := by
        rw [VLevel.inst_inst, genericLevels_inst hlen]; exact hnz
      have := famProp_false_of_neverZero H hfamd hsem hsemL hkuv hnz' hlevel c
        (List.range nf).reverse (ls := target :: levels)
      rw [this] at hfp; cases hfp
    · exact .inl fun v => by
        show target.eval v = 0
        rw [VLevel.equiv_def.1 htz]; rfl

end

end Lean4Lean.ShapeModel
