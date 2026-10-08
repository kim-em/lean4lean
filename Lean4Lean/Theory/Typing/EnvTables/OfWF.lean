import Lean4Lean.Theory.Typing.EnvTables.OfHistory

/-!
# Environment tables

For a well-formed environment, `ctorOf env` and `famOf env` are chosen from the tables built along
one of its histories (`Tables.OfHistory`, `EnvTablesHist.lean`). They record, for every family, its
*first* registration: native installation (families with at least one constructor), structure
registration, eliminator registration (family by family, for a family none of whose names was
recorded before) or the quotient.

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

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

variable {env : VEnv}

/-- The tables chosen for an environment: tables built along one of its histories
(`Tables.OfHistory`, `EnvTablesHist.lean`; empty if it has none). -/
noncomputable def envTables (env : VEnv) : Tables := by
  classical
  exact if h : ∃ T : Tables, Tables.OfHistory env T then Classical.choose h else Tables.empty

theorem envTables_hist (H : env.WF) : Tables.OfHistory env (envTables env) := by
  classical
  have h := VEnv.WF'.tablesOfHistory H.choose_spec
  simp only [envTables, dif_pos h]
  exact Classical.choose_spec h

theorem envTables_inv (H : env.WF) : (envTables env).Inv env :=
  (envTables_hist H).inv.1

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

/-! ## T5: equations with the same head -/

end Lean4Lean.EnvTables
