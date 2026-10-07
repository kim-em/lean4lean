import Lean4Lean.Theory.Typing.ProjectionCornerWalk
import Lean4Lean.Theory.Typing.TelescopeTransport
import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.CanonicalChoice
import Lean4Lean.Theory.Typing.ProjectionShape

/-!
# An inhabitant of a field type of a non-eliminable structure field

At a typed major `e : S params` of a registered structure `S`, the binder type `D` that the
projection walk reaches for a field whose projection fails the universe guard is inhabited,
when the environment has canonical choice and `S` can be eliminated into `Prop`: the recursor of
`S` with the constant motive `fun _ => Nonempty D` and the minor premise
`fun fields => Nonempty.intro field` gives `Nonempty D`, and `Classical.choice` gives a term of
`D`. The minor premise is typed because every projection used by `D` is a proof field
(`VProjectionInfo.field_of_walk`).
-/

namespace Lean4Lean
open VExpr VEnv InductiveSignature

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem takeForalls_eq_wrapForalls' :
    ∀ {n : Nat} {type result : VExpr} {domains : List VExpr},
      type.takeForalls n = some (domains, result) →
      type = VExpr.wrapForalls domains result ∧ domains.length = n
  | 0, type, result, domains, H => by
    cases Option.some.inj H
    exact ⟨rfl, rfl⟩
  | n + 1, type, result, domains, H => by
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls n with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rw [VExpr.takeForalls, htail] at H
        cases Option.some.inj H
        have ih := takeForalls_eq_wrapForalls' htail
        exact ⟨congrArg (VExpr.forallE domain) ih.1, by simp [ih.2]⟩
    | _ => simp [VExpr.takeForalls] at H

theorem IsDefEqU.wrapForalls_context' (henv : env.WF) (hΓ : OnCtx Γ₀ (env.IsType U))
    (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (hlen : domains.length = domains'.length)
    (ht : IsDefEqU env U Γ₁ (VExpr.wrapForalls domains result)
      (VExpr.wrapForalls domains' result')) :
    IsDefEqCtx env U Γ₀ (domains.reverse ++ Γ₁) (domains'.reverse ++ Γ₂) := by
  induction domains generalizing Γ₁ Γ₂ domains' with
  | nil =>
    have he : domains' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst domains'
    exact W
  | cons d ds ih =>
    cases domains' with
    | nil => simp at hlen
    | cons d' ds' =>
      obtain ⟨⟨u, hd⟩, _, hrest⟩ := ht.forallE_inv henv (W.isType' hΓ)
      have hh := ih (.succ W hd)
        (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen) ⟨_, hrest⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hh

/-- The parameters of a typed major of a registered structure without indices are typed along
the parameter telescope of the structure's constructor, and the major has no index arguments. -/
theorem HasType.structure_params (henv : env.WF) (hΔ : OnCtx Δ (env.IsType U))
    (hinfo : env.projections S info) (hls : ∀ l ∈ ls, l.WF U) (hni : info.nindices = 0)
    {ps : List VExpr} (hpl : ps.length = info.nparams)
    (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx))) :
    idx = [] ∧ ∃ ctorParams tail,
      info.ctorType.takeForalls info.nparams = some (ctorParams, tail) ∧
      TelInst env U Δ (ctorParams.map (·.instL ls)) ps := by
  obtain ⟨typeConst, normalized, ownParams, rest, exprType, ctorParams, tail, hlookup, hnorm,
    hown, hctorP, hctx, indices, result, hind, hres⟩ := Ordered.projectionShape_params henv hinfo
  rw [hni] at hind
  cases Option.some.inj hind
  simp only [List.reverse_nil, List.nil_append] at hres
  obtain ⟨v, hTy⟩ := he'.isType henv.ordered hΔ
  have hhead := VExpr.WF.of_mkApps henv.ordered hΔ (f := .const S ls) ⟨_, hTy⟩
  obtain ⟨_, hhead⟩ := hhead
  obtain ⟨ci, hci, _, hlen⟩ := HasType.const_inv henv.ordered hΔ hhead
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hconst : env.HasType U Δ (.const S ls) (typeConst.type.instL ls) := .const hlookup hls hlen
  have hnormL := (hnorm.instL hls).weak0 henv.ordered (Γ := Δ)
  have hconst' := hconst.defeqU_r henv hΔ ⟨_, hnormL⟩
  obtain ⟨hshapeN, hownl⟩ := takeForalls_eq_wrapForalls' hown
  rw [hshapeN, VExpr.instL_wrapForalls] at hconst'
  have hprefixWF : VExpr.WF env U Δ (VExpr.mkApps (.const S ls) ps) := by
    rw [VExpr.mkApps_append] at hTy
    exact VExpr.WF.of_mkApps henv.ordered hΔ ⟨_, hTy⟩
  obtain ⟨hargs, happ⟩ := HasType.mkApps_wrapForalls henv hΔ hconst' hprefixWF
    (by simp [hownl, hpl])
  have hOwn : TelInst env U Δ (ownParams.map (·.instL ls)) ps :=
    ⟨by simp [hownl, hpl], hargs⟩
  refine ⟨?_, ctorParams, tail, hctorP, ?_⟩
  · -- the family applied to its parameters is a sort, so no further argument fits
    cases idx with
    | nil => rfl
    | cons a as =>
      exfalso
      rw [VExpr.mkApps_append] at hTy
      have hfa := VExpr.WF.of_mkApps henv.ordered hΔ (f := .app _ a) ⟨_, hTy⟩
      obtain ⟨A, B, hfun, _⟩ := hfa.app_inv henv.ordered hΔ
      have hTC : env.IsType U [] (typeConst.type.instL ls) :=
        (henv.ordered.constWF hlookup).instL hls
      have hNT : env.IsType U [] (normalized.instL ls) :=
        IsType.defeqU_l henv trivial ⟨_, hnorm.instL hls⟩ hTC
      rw [hshapeN, VExpr.instL_wrapForalls] at hNT
      have hΔo : OnCtx (ownParams.map (·.instL ls)).reverse (env.IsType U) := by
        simpa using (IsType.wrapForalls_inv henv (Γ := []) trivial hNT).1
      have hresL : env.IsDefEq U (ownParams.map (·.instL ls)).reverse (rest.instL ls)
          (.sort (info.resultLevel.inst ls)) (.sort (info.resultLevel.inst ls).succ) := by
        simpa [List.map_reverse, VExpr.instL, VLevel.inst] using hres.instL hls
      have hinst := IsDefEq.closed_instOuter_congr henv hΔ hΔo hresL hOwn.1 hOwn.1
        (fun j hj _ hd => hOwn.2 j hj hd)
      simp only [VExpr.instOuter_sort] at hinst
      have h1 := happ.uniqU henv hΔ hfun
      exact IsDefEqU.sort_forallE_inv henv hΔ ((IsDefEq.toU hinst).symm.trans henv hΔ h1)
  · exact TelInst.of_ctxDefEq henv hΔ hOwn (by simpa [List.map_reverse] using hctx.instL hls)

/-- Constructor parameters typed along the source constructor are typed along the normalized
signature's parameter telescope. -/
theorem TelInst.signature_params {s : InductiveSignature} {c : InductiveSignature.Constructor s.families.size}
    (henv : env.WF) (hΔ : OnCtx Δ (env.IsType U)) (hls : ∀ l ∈ ls, l.WF U)
    {ctorType tail : VExpr} {ctorParams : List VExpr} {ps : List VExpr}
    (hctorP : ctorType.takeForalls s.params.length = some (ctorParams, tail))
    (hdef : env.IsDefEqU s.uvars [] (s.constructorType c) ctorType)
    (H : TelInst env U Δ (ctorParams.map (·.instL ls)) ps) :
    TelInst env U Δ (s.params.map (·.instL ls)) ps := by
  obtain ⟨hshape, hlen⟩ := takeForalls_eq_wrapForalls' hctorP
  rw [hshape, InductiveSignature.constructorType, VExpr.wrapForalls_append] at hdef
  have hctx := IsDefEqU.wrapForalls_context' henv (Γ₀ := []) trivial .zero hlen.symm hdef
  simp only [List.append_nil] at hctx
  have hctxL := (IsDefEqCtx.instL hls hctx).symm henv.ordered
  exact TelInst.of_ctxDefEq henv hΔ H (by simpa [List.map_reverse] using hctxL)

end VEnv

namespace InductiveSignature.NativeRecursorData
variable {env : VEnv} {data : NativeRecursorData}

/-- The recursor of an ordinary (one-family) declaration is installed with its generated type,
and the declaration's constructor is, in the empty context, definitionally the installed
constructor. -/
theorem NativeRecursorRegistered.ordinary (H : NativeRecursorRegistered env data)
    (hfam : data.schema.signature.families.size = 1)
    (hcs : data.schema.signature.constructors.size = 1)
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
  have hrest : data.schema.restoration = {} := hr.trans (hdata.restoration_of_singleton hfam)
  have haux := hdata.noAuxiliaries_of_singleton hfam
  subst haux
  refine ⟨?_, ?_⟩
  · have hgen : data.recursorType = some (data.nativeInstance.recursorType data.owner) := by
      simp [recursorType, hrest]
    exact Hcopy.recursorType hgen
  -- the correspondence of the normalized and source declarations
  obtain ⟨envTypes, direct, hadd, hdirect, _, hcorr⟩ := hdata.correspondence
  have hdir : direct = [] := by
    simpa using hdirect.symm
  subst hdir
  simp only [List.append_nil] at hcorr
  have hrest' : compilationRestoration source [] = {} := hdata.restoration_of_singleton hfam
  rw [hrest'] at hcorr
  -- the single family and constructor of the signature
  have hfams : data.schema.signature.families.toList = [data.schema.signature.families[0]'(by omega)] :=
    Instance.toList_of_size_one _ hfam ⟨0, by omega⟩
  have hctors : data.schema.signature.constructors.toList = [data.schema.signature.constructors[i]] :=
    Instance.toList_of_size_one _ hcs i
  have hown : (data.schema.signature.constructors[i]).owner.val = 0 := by
    have := (data.schema.signature.constructors[i]).owner.isLt; omega
  simp only [declaration, hfams, hctors, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
    List.map_nil, List.filterMap_cons, List.filterMap_nil, hown, if_true] at hcorr
  obtain ⟨srcS, hsrcS⟩ : ∃ srcS, source.types = [srcS] := by
    have h := hcorr
    generalize source.types = st at h
    cases h with
    | cons _ t => cases t; exact ⟨_, rfl⟩
  rw [hsrcS] at hcorr
  have hRF := (List.forall₂_cons.1 hcorr).1
  obtain ⟨srcC, hsrcC⟩ : ∃ srcC, srcS.ctors = [srcC] := by
    have h := hRF.constructors
    generalize srcS.ctors = sc at h
    cases h with
    | cons _ t => cases t; exact ⟨_, rfl⟩
  have hCC := hRF.constructors
  rw [hsrcC] at hCC
  obtain ⟨hcn, hcu, restored, hres, hdef⟩ := (List.forall₂_cons.1 hCC).1
  simp only [Restoration.expr_empty, Option.some.injEq] at hres
  subst hres
  -- the source constructor is the installed constructor
  have hinstC : env.constants srcC.name = some srcC.toVConstant := by
    refine he.constants (VInductBlock.install_ctor_lookup hi ?_)
    rw [hdata.ctors, VInductDecl.constructorConstants, hsrcS]
    simp [hsrcC]
  have hsame : srcC.name = ctorName := by rw [← hcn, ← hname]
  rw [hsame, hctor] at hinstC
  cases Option.some.inj hinstC
  refine ⟨by simpa using hcu.symm, envTypes, ?_, ?_⟩
  · -- the checked headers are installed
    have hinst := hi
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinst
    obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
    have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
      (VEnv.addEliminators_addProjections_le.trans ((VEnv.addConstVals_le he3).trans
        (VEnv.addDefEqRules_le.trans he)))
    rw [hdata.types] at he1
    exact (VEnv.addConstVals_mono hbase hadd he1).trans hle1
  · have huv : srcS.uvars = data.schema.signature.uvars := by
      rw [← hRF.universes]
    have : source.uvars = data.schema.signature.uvars := by
      rw [← hdata.uvars, hdata.model.uvars]
    rw [← this]
    simpa using hdef

end InductiveSignature.NativeRecursorData
end Lean4Lean
