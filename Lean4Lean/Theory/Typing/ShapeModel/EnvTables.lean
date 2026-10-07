import Lean4Lean.Theory.Typing.ShapeModel.EnvTablesRegistration

/-!
# Environment tables for the shape model (M4a, T1 (a), (b), (d), (e), T4, T5 (a)-(c))

For a well-formed environment, `ctorOf env` and `famOf env` are chosen from the history tables of
`EnvTablesRegistration.lean` (`VEnv.WF.tables`). They record, for every family, its *first*
registration: native installation (families with at least one constructor), structure
registration, eliminator registration (when none of its names was recorded before) or the
quotient.

## Why first registrations

The same constants can be registered under two different splits into parameters and fields, so
no table can agree with all registrations. Counterexample (all steps are allowed by `VEnv.WF'`):
add axioms `S : Type → Type 1` and `S.mk : (α : Type) → α → S α`; register them with
`inductProjections` for the declaration with one parameter (`structure S (α : Type) : Type 1`,
one field `val : α`), giving `projections S ⟨.., nparams := 1, .., ctorName := S.mk, ..⟩` with one
field; then register an eliminator schema (`inductEliminators`) for the declaration with no
parameters and one index (`inductive S : Type → Type 1 | mk (α : Type) (a : α) : S α`), whose
generic case equation has the major `S.mk α a` with *two* trailing field variables. Target
T1 (d) forces `ctorOf S.mk = ⟨S, 0, 1, 1⟩` while T1 (c) for the schema equation forces two fields.
The tables keep the first registration (here the structure one); T1 (c) is stated for schema
equations whose family view is the recorded one.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

variable {env : VEnv}

/-- The tables chosen for an environment (empty if it has none). -/
noncomputable def envTables (env : VEnv) : Tables := by
  classical
  exact if h : ∃ T : Tables, T.Inv env then Classical.choose h else Tables.empty

theorem envTables_inv (H : env.WF) : (envTables env).Inv env := by
  classical
  have h := VEnv.WF.tables H
  simp only [envTables, dif_pos h]
  exact Classical.choose_spec h

/-- The constructor table. -/
noncomputable def ctorOf (env : VEnv) : Name → Option CtorData := (envTables env).ctor

/-- The family table. -/
noncomputable def famOf (env : VEnv) : Name → Option FamData := (envTables env).fam

/-! ## T1 (a): constructor shape -/

theorem ctorOf_shape (H : env.WF) (h : ctorOf env c = some k) :
    ∃ ci doms indices, env.constants c = some ci ∧ ci.uvars = k.uvars ∧
      ci.type = VExpr.wrapForalls doms (VExpr.mkApps (.const k.family (VLevel.params k.uvars))
        (vars k.nparams k.nfields ++ indices)) ∧
      doms.length = k.nparams + k.nfields :=
  ((envTables_inv H).views.ctor h).1

/-! ## T1 (b): rigidity and roles -/

theorem ctorOf_rigid (H : env.WF) (h : ctorOf env c = some k) :
    env.Rigid c ∧ env.Rigid k.family ∧ ctorOf env k.family = none := by
  have HT := envTables_inv H
  obtain ⟨_, d, hd, _⟩ := HT.views.ctor h
  refine ⟨HT.views.rigid (.inr (by simp [ctorOf] at h; simp [h])),
    HT.views.rigid (.inl (by simp [hd])), HT.views.fam_ctor (by simp [hd])⟩

/-! ## T1 (d): projections -/

theorem ctorOf_projection (H : env.WF) (h : env.projections s info) :
    ctorOf env info.ctorName = some ⟨s, info.uvars, info.nparams, info.numFields⟩ :=
  ((envTables_inv H).projections h).2

/-! ## T1 (e): families -/

/-- The family type is *definitionally* (not syntactically) a telescope of `nparams + nindices`
binders ending in the recorded sort: inductive headers are checked up to definitional equality
(`VInductDecl.TypeShape`), so a family may be declared with a type that only reduces to a
telescope. -/
theorem famOf_shape (H : env.WF) (h : famOf env I = some d) :
    ∃ ci, env.constants I = some ci ∧ ci.uvars = d.uvars ∧
      ∃ doms result type, env.IsDefEq d.uvars [] ci.type (VExpr.wrapForalls doms result) type ∧
        doms.length = d.nparams + d.nindices ∧
        env.IsDefEq d.uvars doms.reverse result (.sort d.resultLevel) (.sort d.resultLevel.succ) :=
  ((envTables_inv H).views.fam h).1

theorem famOf_nodup (H : env.WF) (h : famOf env I = some d) : d.ctors.Nodup :=
  ((envTables_inv H).views.fam h).2.1

theorem famOf_mem_ctors (H : env.WF) (h : famOf env I = some d) :
    c ∈ d.ctors ↔ ∃ k, ctorOf env c = some k ∧ k.family = I := by
  have HT := envTables_inv H
  constructor
  · intro hc
    obtain ⟨k, hk, hfam, _⟩ := (HT.views.fam h).2.2 c hc
    exact ⟨k, hk, hfam⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨_, d', hd', hc⟩ := HT.views.ctor hk
    simp only [famOf] at h
    rw [h] at hd'
    cases hd'
    exact hc

theorem ctorOf_famOf (H : env.WF) (h : ctorOf env c = some k) :
    ∃ d, famOf env k.family = some d ∧ d.uvars = k.uvars ∧ d.nparams = k.nparams := by
  have HT := envTables_inv H
  obtain ⟨_, d, hd, hc⟩ := HT.views.ctor h
  obtain ⟨k', hk', _, huv, hnp⟩ := (HT.views.fam hd).2.2 c hc
  simp only [ctorOf] at h
  rw [h] at hk'
  cases hk'
  exact ⟨d, hd, huv.symm, hnp.symm⟩

/-- Projection families have exactly the registered constructor, at the registered (equal, not
merely equivalent) result level. -/
theorem famOf_projection (H : env.WF) (h : env.projections s info) :
    famOf env s = some ⟨info.uvars, info.nparams, info.nindices, info.resultLevel,
      [info.ctorName]⟩ :=
  ((envTables_inv H).projections h).1

/-! ## Equation heads -/

/-- The head of a stored equation, after its outer lambdas. -/
def VDefEq.head (df : VDefEq) : VExpr := df.lhs.stripLams.getAppFnArgs.1

theorem definition_head (v : VDefVal) :
    VDefEq.head v.toDefEq = .const v.name (VLevel.params v.uvars) := rfl

theorem quot_head : VDefEq.head quotDefEq = .const ``Quot.lift [.param 0, .param 1] := rfl

theorem native_head {T : Tables} (HT : T.Inv env) (hd : T.natives n = some data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df) :
    VDefEq.head df = .const data.name (VLevel.params data.uvars) := by
  obtain ⟨_, he⟩ := HT.natives hd
  exact he.registered.equation_head howner hgen

/-! ## T4: rigid constants -/

/-- Rigidity is exactly heading no equation. -/
theorem rigid_iff : env.Rigid c ↔ ¬∃ df, env.defeqs df ∧ ∃ ls, VDefEq.head df = .const c ls := by
  constructor
  · rintro h ⟨df, hdf, ls, hh⟩
    exact h df hdf ls hh
  · intro h df hdf ls hh
    exact h ⟨df, hdf, ls, hh⟩

/-- Every head of an equation is a definition, a native recursor, or `Quot.lift`. -/
theorem head_classification {T : Tables} (HT : T.Inv env) (hdf : env.defeqs df)
    (hh : VDefEq.head df = .const c ls) :
    T.defs c ≠ none ∨ T.natives c ≠ none ∨ (T.quot = true ∧ c = ``Quot.lift) := by
  rcases HT.equations hdf with ⟨v, hv, rfl⟩ | ⟨hq, rfl⟩ | ⟨data, hd, index, howner, hgen⟩
  · rw [definition_head] at hh
    cases hh
    exact .inl (by simp [hv])
  · rw [quot_head] at hh
    cases hh
    exact .inr (.inr ⟨hq, rfl⟩)
  · rw [native_head HT hd howner hgen] at hh
    cases hh
    exact .inr (.inl (by simp [hd]))

/-- T4: `Quot.ind` is rigid once the quotient declaration is in the history. (Without the
quotient declaration a definition may be named `Quot.ind`.) -/
theorem quotInd_rigid {ds : List VDecl} (H : env.WF' ds) (hq : VDecl.quot ∈ ds) :
    env.Rigid ``Quot.ind := by
  obtain ⟨T, HT, hquot⟩ := VEnv.WF'.tables H
  obtain ⟨_, _, _, _, _, hdefs, hnat⟩ := HT.quot (hquot hq)
  intro df hdf ls hh
  rcases head_classification HT hdf hh with h | h | ⟨_, he⟩
  · exact h hdefs
  · exact h hnat
  · exact absurd he (by decide)

/-! ## T5: equations with the same head -/

/-- T5 (a)/(c): two distinct equations with the same head constant are native equations of the
same recursor data (the table's entry for that head), at distinct constructor indices with
distinct major constructor names. In particular definition, quotient and native heads are
pairwise distinct. -/
theorem same_head {T : Tables} (HT : T.Inv env) (h1 : env.defeqs df₁) (h2 : env.defeqs df₂)
    (hh1 : VDefEq.head df₁ = .const c ls₁) (hh2 : VDefEq.head df₂ = .const c ls₂)
    (hne : df₁ ≠ df₂) :
    ∃ data, T.natives c = some data ∧ data.name = c ∧ VEnv.NativeRecursorRegistered env data ∧
      ∃ i j : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[i].owner = data.owner ∧
        data.schema.signature.constructors[j].owner = data.owner ∧
        data.equation i = some df₁ ∧ data.equation j = some df₂ ∧ i ≠ j ∧
        data.schema.restoration.headName data.schema.signature.constructors[i].name ≠
          data.schema.restoration.headName data.schema.signature.constructors[j].name := by
  have hdq : T.quot = true → T.defs ``Quot.lift = none ∧ T.natives ``Quot.lift = none :=
    fun hq => ⟨(HT.quot hq).2.2.2.1, (HT.quot hq).2.2.2.2.1⟩
  have hname : ∀ {df n ls' ls''}, VDefEq.head df = .const n ls' →
      VDefEq.head df = .const c ls'' → n = c := fun h h' => (VExpr.const.inj (h.symm.trans h')).1
  rcases HT.equations h1 with ⟨v₁, hv₁, rfl⟩ | ⟨hq₁, rfl⟩ | ⟨d₁, hd₁, i, hi, hg₁⟩ <;>
  rcases HT.equations h2 with ⟨v₂, hv₂, rfl⟩ | ⟨hq₂, rfl⟩ | ⟨d₂, hd₂, j, hj, hg₂⟩
  · have e1 := hname (definition_head v₁) hh1
    have e2 := hname (definition_head v₂) hh2
    rw [e1] at hv₁; rw [e2, hv₁] at hv₂; cases hv₂
    exact absurd rfl hne
  · have e1 := hname (definition_head v₁) hh1
    have e2 := hname quot_head hh2
    rw [e1, ← e2, (hdq hq₂).1] at hv₁; cases hv₁
  · have e1 := hname (definition_head v₁) hh1
    have e2 := hname (native_head HT hd₂ hj hg₂) hh2
    rw [e1, ← e2] at hv₁
    rw [HT.defs_natives (by simp [hv₁])] at hd₂; cases hd₂
  · have e1 := hname quot_head hh1
    have e2 := hname (definition_head v₂) hh2
    rw [e2, ← e1, (hdq hq₁).1] at hv₂; cases hv₂
  · exact absurd rfl hne
  · have e1 := hname quot_head hh1
    have e2 := hname (native_head HT hd₂ hj hg₂) hh2
    rw [e2, ← e1, (hdq hq₁).2] at hd₂; cases hd₂
  · have e1 := hname (native_head HT hd₁ hi hg₁) hh1
    have e2 := hname (definition_head v₂) hh2
    rw [e2, ← e1] at hv₂
    rw [HT.defs_natives (by simp [hv₂])] at hd₁; cases hd₁
  · have e1 := hname (native_head HT hd₁ hi hg₁) hh1
    have e2 := hname quot_head hh2
    rw [e1, ← e2, (hdq hq₂).2] at hd₁; cases hd₁
  · have e1 := hname (native_head HT hd₁ hi hg₁) hh1
    have e2 := hname (native_head HT hd₂ hj hg₂) hh2
    rw [e2, ← e1, hd₁] at hd₂
    cases hd₂
    have hreg := (HT.natives hd₁).2.registered
    refine ⟨d₁, e1 ▸ hd₁, e1, hreg, i, j, hi, hj, hg₁, hg₂, ?_, ?_⟩
    · rintro rfl
      rw [hg₁] at hg₂
      exact hne (Option.some.inj hg₂)
    · intro hn
      have := hreg.constructor_index_unique hi hj hn
      subst this
      rw [hg₁] at hg₂
      exact hne (Option.some.inj hg₂)

/-- T5 (b): a definition head has exactly one equation. -/
theorem definition_head_exclusive (H : env.WF) {v : VDefVal}
    (hdef : env.defeqs v.toDefEq) (hdf : env.defeqs df)
    (hh : VDefEq.head df = .const v.name ls) : df = v.toDefEq := by
  have HT := envTables_inv H
  have hq : (envTables env).quot = true → (envTables env).defs ``Quot.lift = none :=
    fun hq => (HT.quot hq).2.2.2.1
  rcases HT.equations hdef with ⟨w, hw, hvw⟩ | ⟨_, hvq⟩ | ⟨d, hd, i, hi, hg⟩
  · have hname : w.name = v.name := by
      have := congrArg VDefEq.head hvw
      rw [definition_head, definition_head] at this
      exact (VExpr.const.inj this).1.symm
    rcases HT.equations hdf with ⟨u, hu, rfl⟩ | ⟨hq', rfl⟩ | ⟨d, hd, j, hj, hg⟩
    · have e := (VExpr.const.inj ((definition_head u).symm.trans hh)).1
      rw [e, ← hname, hw] at hu
      cases hu
      exact hvw.symm
    · have e := (VExpr.const.inj (quot_head.symm.trans hh)).1
      rw [hname, ← e, hq hq'] at hw
      cases hw
    · have e := (VExpr.const.inj ((native_head HT hd hj hg).symm.trans hh)).1
      rw [e, ← hname, HT.defs_natives (by simp [hw])] at hd
      cases hd
  · have := congrArg VDefEq.lhs hvq
    simp [VDefVal.toDefEq, quotDefEq] at this
  · obtain ⟨fn, levels, args, hm⟩ := (HT.natives hd).2.registered.equation_major hg
    have hl : v.toDefEq.lhs.stripLams = .const v.name (VLevel.params v.uvars) := rfl
    rw [hl] at hm
    cases hm

end Lean4Lean.ShapeModel
