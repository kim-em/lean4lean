import Lean4Lean.Theory.Typing.ShapeModel.RuleValidSingleton

/-!
# Unread fields of singleton-eliminating native rules

Under singleton elimination (one family, at most one constructor, every field a proof or a literal
index of the constructor's result), the fields that the rule does not read (`fieldIndexOf` gives
`none`) are proofs in the header environment of the installation, so their keys are bottom under
any valuation fitting the rule's binder telescope.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem forall₂_some_eq : ∀ {l l' : List VExpr},
    List.Forall₂ (fun a b => some a = some b) l l' → l = l'
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by cases h; rw [forall₂_some_eq t]

theorem insertBinders_map_instL (Xs : List VExpr) (m : Nat) (ls : List VLevel) :
    (insertBinders Xs m).map (·.instL ls) = insertBinders (Xs.map (·.instL ls)) m := by
  simp [insertBinders, List.zipIdx_map, Function.comp_def]

theorem insertBinders_length (Xs : List VExpr) (m : Nat) : (insertBinders Xs m).length = Xs.length :=
  by simp [insertBinders]

theorem insertBinders_getElem (Xs : List VExpr) (m i : Nat) (h : i < (insertBinders Xs m).length) :
    (insertBinders Xs m)[i] = (Xs[i]'(by simpa [insertBinders_length] using h)).liftN m i := by
  simp [insertBinders]

theorem reverse_take_insertBinders (Xs : List VExpr) (m i : Nat) :
    ((insertBinders Xs m).take i).reverse =
      ((Xs.take i).reverse).mapIdx (fun t R => R.liftN m ((Xs.take i).reverse.length - 1 - t)) := by
  apply List.ext_getElem (by simp [insertBinders_length])
  intro t h1 h2
  simp only [List.getElem_mapIdx, List.getElem_reverse, List.getElem_take, List.length_reverse,
    List.length_take, insertBinders_length]
  rw [insertBinders_getElem]

theorem fieldTypes_length (s : InductiveSignature) (ctor : Constructor s.families.size) :
    (s.fieldTypes ctor).length = ctor.fields.length := by simp [fieldTypes]

theorem fieldTypes_getElem (s : InductiveSignature) (ctor : Constructor s.families.size) (i : Nat)
    (h : i < (s.fieldTypes ctor).length) :
    (s.fieldTypes ctor)[i] = s.fieldType i (ctor.fields[i]'(by simpa [fieldTypes_length] using h)) := by
  simp [fieldTypes]

theorem forall₂_expr_empty : ∀ {l l' : List VExpr},
    List.Forall₂ (fun d d' => ({} : Restoration).expr d = some d') l l' → l' = l
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by
    rw [Restoration.expr_empty] at h; cases h; rw [forall₂_expr_empty t]

/-- The unread fields of a singleton-eliminating native rule are bottom. -/
theorem native_singleton_unread (H : env.WF) {E E' cbase envX : VEnv}
    {decl expanded : VInductDecl} {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization}
    (hgood : Good env E) (hEW : E.WF) (hle : E' ≤ env) (hblock : VInductBlock.WF E block)
    (hinstall : block.install E = some E') (hcle : cbase ≤ E)
    (hdata : CompilationData cbase decl expanded s g aux block)
    (hX : cbase.addConstVals expanded.typeConstants = some envX)
    (hsing : s.SingletonElimination envX g.uvars g.levels)
    (hGwf : ∀ l ∈ g.levels, l.WF g.uvars)
    (j : Fin s.constructors.size) {Ds idx : List VExpr}
    (hDsR : List.Forall₂ (fun d d' => (compilationRestoration decl aux).expr d = some d')
        (g.params ++ g.motives ++ g.minors ++
          insertBinders ((s.fieldTypes s.constructors[j]).map (·.instL g.levels))
            (s.families.size + s.constructors.size)) Ds)
    (hidxR : (s.constructors[j].indices.map fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) s.constructors[j].fields.length).mapM
          (compilationRestoration decl aux).expr = some idx)
    (ls : List VLevel) (npre q : Nat) :
    letI := envSig env
    ∀ σ, Valuation.Fits env [] ((Ds.map (·.instL ls)).reverse ++ []) σ →
      ∀ i < s.constructors[j].fields.length,
        (fieldIndexOf (vars npre s.constructors[j].fields.length ++ idx) npre
          s.constructors[j].fields.length q)[i]? = some none →
        σ (s.constructors[j].fields.length - 1 - i) ≤ .bot := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  intro σ W i hi hnone
  obtain ⟨hnotin, -⟩ := fieldIndexOf_none hi hnone
  -- one family: no auxiliaries, identity restoration
  obtain ⟨envTypes0, direct, -, hdirect, -, hfamilies⟩ := hdata.correspondence
  have hlenFam := Lean4Lean.List.Forall₂.length_eq hfamilies
  have hlenDirect := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hdirect)
  have hsrcPos : 0 < decl.types.length := List.length_pos_iff.mpr hdata.sourceWF.1
  rw [declaration_types_length, hsing.1, List.length_append] at hlenFam
  have hauxNil : aux = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hauxNil
  have hsrcLen : decl.types.length = 1 := by omega
  have hr0 : compilationRestoration decl [] = {} := rfl
  rw [hr0] at hDsR hidxR
  have hDs := forall₂_expr_empty hDsR
  have hidx := forall₂_expr_empty (List.mapM_eq_some.mp hidxR)
  subst hDs hidx
  -- the field is a proof
  have hmemc : s.constructors[j] ∈ s.constructors.toList := Array.getElem_mem_toList ..
  rcases (hsing.2.2 _ hmemc i hi).symm with hmem | hp
  · exfalso
    refine hnotin (List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem, ?_⟩))
    simp only [VExpr.instL, VExpr.liftN, liftVar_lt (show s.constructors[j].fields.length - 1 - i <
      s.constructors[j].fields.length by omega)]
  -- the header environment of the installation
  obtain ⟨Et, envC, envR, ht', hc', hr', hE'eq⟩ := install_parts hinstall
  obtain ⟨Et2, -, -, ht2, -, -, htypesWF, -⟩ := hblock
  cases Option.some.inj (ht2.symm.trans ht')
  have hEtord : Et.Ordered := VEnv.Ordered.addConstVals hEW.ordered htypesWF ht'
  have hEtle : Et ≤ env := (VEnv.addConstVals_le hc').trans (VEnv.addEliminators_addProjections_le.trans
    ((VEnv.addConstVals_le hr').trans (hE'eq ▸ VEnv.addDefEqRules_le))) |>.trans hle
  have hgoodEt : Good env Et := hgood.of_parts
    (fun df h => by rwa [VEnv.addConstVals_defeqs ht'] at h)
    (fun h => by rwa [VEnv.addConstVals_eliminators ht'] at h)
    (fun h => by rwa [VEnv.addConstVals_projections ht'] at h)
  have hexpLen : expanded.types.length = 1 := by
    have := Lean4Lean.List.Forall₂.length_eq hdata.model.families
    rw [declaration_types_length, hsing.1] at this
    exact this.symm
  have hheaders : decl.typeConstants = expanded.typeConstants := by
    rw [hdata.headerPrefix, List.take_of_length_le]
    simp [VInductDecl.typeConstants, hexpLen, hsrcLen]
  have hXle : envX ≤ Et := by
    refine addConstVals_le_of hX (hcle.trans (VEnv.addConstVals_le ht')) (fun ci hci => ?_)
    rw [← hheaders, ← hdata.types] at hci
    exact VEnv.addConstVals_get ht' hci
  -- the context of the field is well formed
  obtain ⟨src, -, -, -, A, hdef⟩ := Models.constructor hdata.model j hX
  have hty := VEnv.HasType.mono hXle hdef.hasType.1
  have hctx0 := hasType_wrapForalls_inv hEtord (Γ := []) trivial hty
  have hctx1 := OnCtx.instL' hGwf hctx0
  have hfTl := fieldTypes_length s s.constructors[j]
  have hsplit : List.map (VExpr.instL g.levels)
        ((s.params ++ s.fieldTypes s.constructors[j]).reverse ++ ([] : List VExpr)) =
      (((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).drop i).reverse ++
        ((((s.fieldTypes s.constructors[j]).take i).map (·.instL g.levels)).reverse ++
          (s.params.map (·.instL g.levels)).reverse) := by
    conv => lhs; rw [← List.take_append_drop i (s.fieldTypes s.constructors[j])]
    simp only [List.append_nil, List.reverse_append, List.map_append, List.map_reverse,
      List.map_drop, List.append_assoc]
  rw [hsplit] at hctx1
  have hctx := OnCtx.append_right' hctx1
  have hp' := VEnv.HasType.mono hXle hp
  -- the valuation restricted to the field's context
  have hYlen : (insertBinders (((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map
      (·.instL ls)) (s.families.size + s.constructors.size)).length =
      s.constructors[j].fields.length := by simp [insertBinders_length, fieldTypes_length]
  have hYi : i < (insertBinders (((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map
      (·.instL ls)) (s.families.size + s.constructors.size)).length := by rw [hYlen]; exact hi
  generalize hYL : insertBinders (((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map
      (·.instL ls)) (s.families.size + s.constructors.size) = YL at hYlen hYi
  have htk : YL.take (i + 1) = YL.take i ++ [YL[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hYi]; rfl
  have hrev : YL.reverse = (YL.drop (i + 1)).reverse ++ (YL[i] :: (YL.take i).reverse) := by
    conv => lhs; rw [← List.take_append_drop (i + 1) YL]
    rw [htk]; simp
  have hW : (List.map (VExpr.instL ls) (g.params ++ g.motives ++ g.minors ++
        insertBinders (List.map (VExpr.instL g.levels) (s.fieldTypes s.constructors[j]))
          (s.families.size + s.constructors.size))).reverse ++ ([] : List VExpr) =
      (YL.drop (i + 1)).reverse ++ (YL[i] :: ((YL.take i).reverse ++
        (((g.motives ++ g.minors).map (·.instL ls)).reverse ++ (g.params.map (·.instL ls)).reverse))) := by
    rw [List.map_append, insertBinders_map_instL, hYL, List.reverse_append, hrev]
    simp only [List.append_nil, List.reverse_append, List.map_append, List.append_assoc,
      List.cons_append]
  rw [hW] at W
  have W1 := Valuation.Fits.peel W
  obtain ⟨ρ, x, a, hσ, W2, -, ha, hx⟩ := Valuation.Fits.cons_inv W1
  have hxσ : σ (s.constructors[j].fields.length - 1 - i) = x := by
    have := congrFun hσ 0
    simp only [Valuation.push, List.length_reverse, List.length_drop, hYlen, Nat.add_zero] at this
    rw [show s.constructors[j].fields.length - 1 - i = s.constructors[j].fields.length - (i + 1)
      by omega, this]
  rw [hxσ]
  subst hYL
  rw [reverse_take_insertBinders] at W2
  have hMs : ((g.motives ++ g.minors).map (·.instL ls)).reverse.length =
      s.families.size + s.constructors.size := by
    simp [Instance.motives, Instance.minors]; omega
  rw [← hMs, ← List.append_assoc] at W2
  have W3 := Valuation.Fits.unlift W2
  rw [insertBinders_getElem] at ha
  have ha' := Interp.liftN_iff.1 ha
  have hlenTi : ((((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map
      (·.instL ls)).take i).reverse.length = i := by
    rw [List.length_reverse, List.length_take, List.length_map, List.length_map, fieldTypes_length]
    omega
  rw [hMs, hlenTi] at W3
  have hΓ : List.map (VExpr.instL ls)
      ((((s.fieldTypes s.constructors[j]).take i).map (·.instL g.levels)).reverse ++
        (s.params.map (·.instL g.levels)).reverse) =
      ((((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map (·.instL ls)).take i).reverse ++
        (g.params.map (·.instL ls)).reverse := by
    simp [List.map_reverse, List.map_take, Instance.params]
  have hA : VExpr.instL ls (VExpr.instL g.levels (s.fieldType i s.constructors[j].fields[i])) =
      (((s.fieldTypes s.constructors[j]).map (·.instL g.levels)).map (·.instL ls))[i]'(by
        simp [fieldTypes_length]; exact hi) := by
    simp [fieldTypes_getElem]
  rw [← hΓ] at W3
  rw [← hA] at ha'
  exact proof_key_le_bot H hgoodEt hEtle hEtord hctx hp' ls W3 ha' hx

end

end Lean4Lean.ShapeModel
