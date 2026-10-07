import Lean4Lean.Theory.Typing.ProjectionCornerElim
import Lean4Lean.Theory.Inductive.HypothesisTyping

/-! # The projection-walk corner for declarations with several families -/

namespace Lean4Lean
open VExpr

namespace VExpr

/-- A substitution with its first `e` variables dropped. -/
def Subst.dropN (σ : Subst) (e : Nat) : Subst := fun v => σ (v + e)

theorem liftN_subst_liftN_dropN (d : VExpr) (σ : Subst) (e t : Nat) :
    (d.liftN e t).subst (σ.liftN t) = d.subst ((σ.dropN e).liftN t) := by
  rw [liftN_subst]
  congr 1; funext v
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN, Subst.liftN_apply, Subst.dropN, liftVar]
  by_cases hv : v < t
  · simp [hv]
  · rw [if_neg hv, if_neg (by omega), if_neg hv]
    congr 2; omega

theorem Subst.ofList_append_dropN (ps rest : List VExpr) :
    (Subst.ofList (ps ++ rest)).dropN rest.length = Subst.ofList ps := by
  funext v
  simp only [Subst.dropN, Subst.ofList, List.length_append]
  by_cases hv : v < ps.length
  · rw [dif_pos (by omega), dif_pos hv, List.getElem_append_left (by omega)]
    congr 1; omega
  · rw [dif_neg (by omega), dif_neg hv]
    congr 1; omega

/-- A generated minor premise without constructor indices, instantiated at the parameters and
`rest` (the motives and earlier minors), whose motive is the entry `v` of `rest` from the end. -/
theorem minor_instOuter_gen (F Hs ps rest : List VExpr) (C : VExpr) (v : Nat)
    (hv : v < rest.length) :
    (wrapForalls (InductiveSignature.insertBinders F rest.length ++ Hs)
      (mkApps (.bvar (F.length + Hs.length + v))
        [(C.liftN Hs.length).liftN rest.length (F.length + Hs.length)])).instOuter (ps ++ rest) =
    wrapForalls (F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i)) ++
        Hs.mapIdx (fun k d => d.subst ((Subst.ofList (ps ++ rest)).liftN (F.length + k))))
      ((VExpr.app ((rest[rest.length - 1 - v]'(by omega)).liftN F.length)
        (C.subst ((Subst.ofList ps).liftN F.length))).liftN Hs.length) := by
  rw [instOuter_eq_subst, subst_wrapForalls, VEnv.insertBinders_eq_mapIdx, List.mapIdx_append,
    List.mapIdx_mapIdx]
  simp only [Function.comp_def, liftN_subst_liftN_dropN, Subst.ofList_append_dropN,
    List.length_append, List.length_mapIdx]
  congr 1
  · congr 2; funext k d; rw [Nat.add_comm]
  · show (VExpr.app (.bvar (F.length + Hs.length + v)) _).subst _ = _
    rw [subst_app, subst_bvar, Subst.liftN_apply, if_neg (by omega),
      show F.length + Hs.length + v - (F.length + Hs.length) = v by omega,
      liftN_subst_liftN_dropN, Subst.ofList_append_dropN, liftN_subst_liftN_add,
      Subst.ofList_lt _ (by simp; omega)]
    show _ = VExpr.app _ _
    rw [liftN_liftN, List.getElem_append_right (by simp; omega)]
    congr 3
    simp; omega

/-- The parameter variables beneath `rest`, instantiated. -/
theorem vars_instOuter (ps rest : List VExpr) :
    (InductiveSignature.vars ps.length rest.length).map (·.instOuter (ps ++ rest)) = ps := by
  apply List.ext_getElem (by simp [InductiveSignature.vars])
  intro t h1 h2
  simp only [InductiveSignature.vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]
  rw [VExpr.instOuter_bvar _ (by simp; omega), List.getElem_append_left (by simp; omega)]
  congr 1; simp; omega

end VExpr

namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s)

/-- A motive is the first motive's shape lifted past the earlier motives. -/
theorem motive_liftN (family : Family) (k : Nat) :
    g.motive family k = (g.motive family 0).liftN k := by
  simp only [motive, insertBinders_zero, VEnv.liftN_wrapForalls, List.mapIdx_append,
    List.length_map, Nat.zero_add, length_insertBinders, VExpr.liftN, List.mapIdx_cons,
    List.mapIdx_nil, VExpr.liftN_mkApps, List.map_append]
  congr 2
  · rw [VEnv.insertBinders_eq_mapIdx]
  · rw [VEnv.vars_map_liftN_hi _ _ _ _ (Nat.le_refl _), VEnv.vars_map_liftN_lo _ _ _ _ (by omega),
      Nat.add_comm]

/-- The constructor application of a minor premise, beneath its hypotheses and `extra`
binders between the parameters and the fields. -/
theorem constructorApp_shape_gen (c : Constructor s.families.size) (extra below : Nat) :
    g.constructorApp c extra below =
      ((g.sCtorApp c).liftN below).liftN extra ((g.sFields c).length + below) := by
  have hnf : (g.sFields c).length = c.fields.length := by simp [sFields, fieldTypes]
  simp only [constructorApp, sCtorApp, VExpr.liftN_mkApps, hnf]
  have hv := VEnv.vars_eq_bvarRange c.fields.length 0
  simp only [Nat.add_zero] at hv
  rw [CastSpec.bvarRange_split, ← VEnv.vars_eq_bvarRange, ← hv]
  simp only [List.map_append, List.map_map, Function.comp_def]
  congr 1
  congr 1 <;>
  · simp only [vars, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    simp only [VExpr.liftN, liftVar]
    split <;> split <;> (congr 1; omega)

end InductiveSignature.Instance

theorem List.forall₂_exists_of_mem {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {x}, x ∈ l → ∃ y ∈ l', R x y
  | _, _, .cons h _, _, .head _ => ⟨_, .head _, h⟩
  | _, _, .cons _ t, _, .tail _ hx =>
    let ⟨y, hy, hr⟩ := List.forall₂_exists_of_mem t hx
    ⟨y, .tail _ hy, hr⟩

namespace InductiveSignature.NativeRecursorData

/-- The recursor of a declaration without nested auxiliaries is installed with its generated
type, and each of its constructors is, in the empty context, definitionally the installed
constructor of the same name. -/
theorem NativeRecursorRegistered.unnested {env : VEnv} {data : NativeRecursorData}
    (H : VEnv.NativeRecursorRegistered env data)
    (hrest : data.schema.restoration = {})
    (i : Fin data.schema.signature.constructors.size)
    {ctorName : Name} {ctor : VConstant}
    (hname : data.schema.signature.constructors[i].name = ctorName)
    (hctor : env.constants ctorName = some ctor) :
    env.constants data.name =
      some ⟨data.uvars, data.nativeInstance.recursorType data.owner⟩ ∧
    ctor.uvars = data.schema.signature.uvars ∧
    ∃ envTypes, envTypes ≤ env ∧ envTypes.IsDefEqU data.schema.signature.uvars []
      (data.schema.signature.constructorType data.schema.signature.constructors[i]) ctor.type := by
  have Hcopy := H
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, hbase, hr, _, hu, hl, ht, hi, he⟩ := H
  refine ⟨?_, ?_⟩
  · have hgen : data.recursorType = some (data.nativeInstance.recursorType data.owner) := by
      simp [recursorType, hrest]
    exact Hcopy.recursorType hgen
  have haux : auxiliaries = [] := by
    have h := congrArg Restoration.recursors (hr.symm.trans hrest)
    simp only [compilationRestoration, List.map_eq_nil_iff, List.zipIdx_eq_nil_iff] at h
    exact h
  subst haux
  obtain ⟨envTypes, direct, hadd, hdirect, _, hcorr⟩ := hdata.correspondence
  have hdir : direct = [] := by simpa using hdirect.symm
  subst hdir
  simp only [List.append_nil] at hcorr
  rw [show compilationRestoration source [] = {} from rfl] at hcorr
  -- the normalized family of the constructor and its source family
  obtain ⟨c, hc⟩ : ∃ c, data.schema.signature.constructors[i] = c := ⟨_, rfl⟩
  have hcmem : c ∈ data.schema.signature.constructors.toList := hc ▸ Array.getElem_mem_toList ..
  have hfmem : data.schema.signature.families[c.owner] ∈ data.schema.signature.families.toList :=
    Array.getElem_mem_toList ..
  obtain ⟨T, hT, hTc⟩ : ∃ T ∈ data.schema.signature.declaration.types,
      ({ name := c.name, uvars := data.schema.signature.uvars,
         type := data.schema.signature.constructorType c } : VConstVal) ∈ T.ctors := by
    refine ⟨_, List.mem_map.2 ⟨(data.schema.signature.families[c.owner], c.owner.val),
      ?_, rfl⟩, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp
    · simp only [List.mem_filterMap]
      exact ⟨c, hcmem, by simp⟩
  obtain ⟨src, hsrc, hRF⟩ := List.forall₂_exists_of_mem hcorr hT
  obtain ⟨srcC, hsrcC, hcn, hcu, restored, hres, hdef⟩ :=
    List.forall₂_exists_of_mem hRF.constructors hTc
  simp only [Restoration.expr_empty, Option.some.injEq] at hres
  subst hres
  have hinstC : env.constants srcC.name = some srcC.toVConstant := by
    refine he.constants (VInductBlock.install_ctor_lookup hi ?_)
    rw [hdata.ctors, VInductDecl.constructorConstants]
    exact List.mem_flatMap.2 ⟨src, hsrc, hsrcC⟩
  have hsame : srcC.name = ctorName := by rw [← hcn, ← hname, hc]
  rw [hsame, hctor] at hinstC
  cases Option.some.inj hinstC
  refine ⟨by simpa using hcu.symm, envTypes, ?_, ?_⟩
  · have hinst := hi
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinst
    obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
    have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
      (VEnv.addProjections_le.trans ((VEnv.addConstVals_le he3).trans
        (VEnv.addDefEqRules_le.trans he)))
    rw [hdata.types] at he1
    exact (VEnv.addConstVals_mono hbase hadd he1).trans hle1
  · have : source.uvars = data.schema.signature.uvars := by
      rw [← hdata.uvars, hdata.model.uvars]
    rw [← this, hc]
    simpa using hdef

end InductiveSignature.NativeRecursorData

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Arguments of a closed telescope are typed along it when each is typed at its instantiated
domain, given the earlier ones. -/
theorem TelInst.build (henv : env.WF) {Γ doms args : List VExpr}
    (hdoms : OnCtx doms.reverse (env.IsType U)) (hlen : args.length = doms.length)
    (h : ∀ t (ht : t < doms.length), TelInst env U Γ (doms.take t) (args.take t) →
      env.IsType U Γ (doms[t].instOuter (args.take t)) →
      env.HasType U Γ (args[t]'(by omega)) (doms[t].instOuter (args.take t))) :
    TelInst env U Γ doms args := by
  have key : ∀ t, t ≤ doms.length → TelInst env U Γ (doms.take t) (args.take t) := by
    intro t
    induction t with
    | zero => intro _; simpa using TelInst.nil
    | succ t ih =>
      intro ht
      have ht' : t < doms.length := by omega
      have H := ih (by omega)
      have hc := OnCtx.getElem_reverse_append (Γ := []) (by simpa using hdoms) t ht'
      simp only [List.append_nil] at hc
      obtain ⟨hpre, u, hdt⟩ := hc
      have hI : env.IsType U Γ (doms[t].instOuter (args.take t)) :=
        ⟨u, by simpa using HasType.closed_instOuter henv hpre hdt H⟩
      rw [List.take_succ_eq_append_getElem ht', List.take_succ_eq_append_getElem (by omega)]
      exact TelInst.append_one H (h t ht' H hI)
  have := key doms.length (Nat.le_refl _)
  rwa [List.take_length, List.take_of_length_le (by omega)] at this

end VEnv
end Lean4Lean
