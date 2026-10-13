import Lean4Lean.Theory.Typing.Strengthening.ConstructorComputationObservations
import Lean4Lean.Theory.Typing.Strengthening.ProjectionHeadRigidity

/-! # Structure eta cannot add finite field observations

The registered constructor's observation must ultimately select one field. That
field of an eta expansion is a projection of the original value, so its observation
was already present there. Constructor rigidity excludes declaration-body
observations, and constructor-family uniqueness aligns the selected projection.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions PatternCompute)

/-- Every demanded key is covered by a stronger key in the supplied list. -/
def Ob.Covers (supplied demanded : List Ob) : Prop :=
  ∀ key ∈ demanded, ∃ key' ∈ supplied, Ob.Le key' key

/-- Invert subsumption between function observations. -/
theorem Ob.Le.app_parts (H : Ob.Le (.app K o) (.app L p)) : Ob.Covers L K ∧ Ob.Le o p := by
  cases H with
  | refl => exact ⟨fun key hk => ⟨key, hk, .refl⟩, .refl⟩
  | app f hf hk ho => exact ⟨fun key hkey => ⟨f key, hf key hkey, hk key hkey⟩, ho⟩

/-- Strip equally many curried arguments from a constructor observation. The
remaining result must be the same field, with a subsumed payload. -/
theorem Ob.Le.wrap_field_inv (H : Ob.Le (Ob.wrap keys (.field s i o)) (Ob.wrap keys' result))
    (hlen : keys.length = keys'.length) :
    ∃ result', result = .field s i result' ∧ Ob.Le o result' ∧
      List.Forall₂ (fun K L => Ob.Covers L K) keys keys' := by
  induction keys generalizing keys' with
  | nil =>
    cases keys' with
    | nil =>
      cases H with
      | refl => exact ⟨_, rfl, .refl, .nil⟩
      | field h => exact ⟨_, rfl, h, .nil⟩
    | cons => cases hlen
  | cons K keys ih =>
    cases keys' with
    | nil => cases hlen
    | cons L keys' =>
      obtain ⟨hc, ho⟩ := H.app_parts
      obtain ⟨result', he, hr, hks⟩ := ih ho (Nat.succ.inj hlen)
      exact ⟨result', he, hr, .cons hc hks⟩

variable [Params]
variable {D : Definitions}

/-- Invert all applications at once, retaining a finite demand list per argument. -/
theorem Obs.spine_inv (H : Obs D S (mkApps f args) o) :
    ∃ keys, Obs D S f (Ob.wrap keys o) ∧
      List.Forall₂ (fun K a => ∀ key ∈ K, Obs D S a key) keys args := by
  induction args generalizing f with
  | nil => exact ⟨[], H, .nil⟩
  | cons a args ih =>
    obtain ⟨keys, hf, hargs⟩ := ih H
    obtain ⟨K, hf, ha⟩ := hf.app_inv
    exact ⟨K :: keys, hf, .cons ha hargs⟩

/-- A non-unfolding constant's observation must come from a registered
constructor, followed only by subsumption. -/
theorem Obs.const_ctor_inv (hrigid : Params.env.Rigid c) (hc : ¬ NotEtaCtor c)
    (hn : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (H : Obs D S (.const c ls) o) :
    ∃ s info keys i K key, Params.env.projections s info ∧ info.ctorName = c ∧
      keys.length = info.nparams + info.numFields ∧ keys[info.nparams + i]? = some K ∧
      key ∈ K ∧ Ob.Le (Ob.wrap keys (.field s i key)) o := by
  generalize he : VExpr.const c ls = e at H
  induction H with
  | ctor hi hl hg ho => cases he; exact ⟨_, _, _, _, _, _, hi, rfl, hl, hg, ho, .refl⟩
  | ctorTuple ht => cases he; exact (hc ht).elim
  | recursor hp _ _ =>
    cases he
    exact (hrigid.not_patternHeadsStoredRule (Params.pat_storedRule hp)
      (by simp [Pattern.constHead_eq, SimplePattern.toPattern, Pattern.headConst, Pattern.headConst_varN])).elim
  | delta hd _ => cases he; exact (hn _ _ hd).elim
  | sub _ h ih =>
    obtain ⟨s, info, keys, i, K, key, hi, hn, hl, hg, ho, hs⟩ := ih he
    exact ⟨s, info, keys, i, K, key, hi, hn, hl, hg, ho, hs.trans h⟩
  | var | sort | pi | lam | app | proj => cases he

/-- Structure eta is backwards sound for finite observations. Neither the value
nor the newly chosen parameters need be typed, and the parameters need not be
scoped below any lift. Rigidity of the actual constructor is essential. -/
theorem Obs.struct_eta_back (hinfo : Params.env.projections s info) (hindices : info.nindices = 0)
    (hn : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs) (hps : ps.length = info.nparams)
    (H : Obs D S (structExpand s info ls ps e) o) : Obs D S e o := by
  obtain ⟨keys, hc, hargs⟩ := H.spine_inv
  obtain ⟨s', info', keys', i, K, key, hi, hname, hlen, hget, hkey, hle⟩ := hc.const_ctor_inv (Params.henv.projectionCtorRigid hinfo)
    (fun h => h s info hinfo hindices rfl) hn
  obtain ⟨rfl, rfl⟩ := Params.henv.ordered.projectionConstructor_family hi hinfo hname
  have hlen' : keys'.length = keys.length := by
    have ha := hargs.length_eq
    simp only [List.length_append, List.length_map, List.length_range, hps] at ha
    omega
  obtain ⟨result, rfl, hr, hcover⟩ := hle.wrap_field_inv hlen'
  obtain ⟨K', hget', hc⟩ := select_forall₂ hcover hget
  obtain ⟨key', hk', hkey'⟩ := hc key hkey
  obtain ⟨arg, harg, ho⟩ := select_forall₂ hargs hget'
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.1 hget
  have hidx : i < info'.numFields := by omega
  have he : arg = .proj s' i e := by
    rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left] at harg
    simpa [hidx] using harg.symm
  subst arg
  exact .sub (ho key' hk').proj_inv (.field (hkey'.trans hr))

/-- Actual environment equations satisfy the constructor-rigidity premise. -/
theorem Obs.struct_eta_back_ofEnv (hinfo : Params.env.projections s info)
    (hindices : info.nindices = 0) (hps : ps.length = info.nparams)
    (H : Obs (Definitions.ofEnv Params.env Params.univs Params.henv) S
      (structExpand s info ls ps e) o) :
    Obs (Definitions.ofEnv Params.env Params.univs Params.henv) S e o :=
  H.struct_eta_back hinfo hindices
    (fun _ _ => Definitions.ofEnv_no_rigid Params.henv (Params.henv.projectionCtorRigid hinfo)) hps

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
