import Lean4Lean.Theory.Typing.Strengthening.ProjectionTypeRecovery

/-! # Type recovery parameterized by scoped computation

These certificates reconstruct a chosen type from the term's syntax, variable
lookup, constant declarations, and certified computation on already recovered
types. They require only source well-formedness at replay. Application recovers
its argument type by uniqueness, so it needs no assumed conversion check below.
The syntax covers all expression constructors, including projections with
recovered major families. Completeness for arbitrary typing is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A computation preserves weakening at every finite insertion. -/
def ComputeWeakening (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {n k Γ Γ' e out}, Ctx.LiftN n k Γ Γ' → C Γ e out →
    C Γ' (e.liftN n k) (out.liftN n k)

/-- A computation from a typed lifted source reconstructs its target syntax and
replays at the source's original type below. This interface is verified for each
concrete computation used here; it is not an assumed strengthening principle. -/
def ComputeDescent (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {ρ Γ Γ' e target T}, C Γ' (e.lift' ρ) target → Ctx.Lift' ρ Γ Γ' →
    OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    env.HasType univs Γ e T →
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out T

/-- Recovery computes inferred types, so scoped replay only needs to hold at
sort-typed sources. This permits rules whose validity depends on being types. -/
def TypeComputeDescent (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {ρ Γ Γ' e target u}, C Γ' (e.lift' ρ) target → Ctx.Lift' ρ Γ Γ' →
    OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    env.HasType univs Γ e (.sort u) →
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out (.sort u)

/-- Ordinary computation descent supplies the restricted type interface. -/
theorem ComputeDescent.types (H : ComputeDescent C) : TypeComputeDescent C :=
  fun R W hΓ hΓ' ht => H R W hΓ hΓ' ht

/-- Identity insertion gives ambient replay at the supplied source sort. -/
theorem TypeComputeDescent.replay (hc : TypeComputeDescent C) (R : C Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u)) :
    env.IsDefEq univs Γ e out (.sort u) := by
  have R' : C Γ (e.lift' .refl) out := by simpa using R
  obtain ⟨out₀, ho, H⟩ := hc R' .refl hΓ hΓ ht
  simp only [lift'_refl] at ho
  exact ho.symm ▸ H

/-- Typed replay is the identity-insertion instance of scoped descent. -/
theorem ComputeDescent.simAt (hc : ComputeDescent C) (R : C Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out := by
  intro T ht
  have R' : C Γ (e.lift' .refl) out := by simpa using R
  obtain ⟨out₀, hout, H⟩ := hc R' .refl hΓ hΓ ht
  simp only [lift'_refl] at hout
  exact hout.symm ▸ H

/-- A finite source-typed reconstruction of a particular type. The Pi rule
records only universe choices, which uniqueness reflects without strengthening.
Conversion uses a parameter whose descent is checked separately. -/
inductive TypeRecoveryWith (C : List VExpr → VExpr → VExpr → Prop) : List VExpr → VExpr → VExpr → Prop where
  | sort : u.WF univs → TypeRecoveryWith C Γ (.sort u) (.sort (.succ u))
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
      TypeRecoveryWith C Γ (.const c ls) (ci.type.instL ls)
  | bvar : Lookup Γ i A → TypeRecoveryWith C Γ (.bvar i) A
  | lam : TypeRecoveryWith C (A :: Γ) b B → TypeRecoveryWith C Γ (.lam A b) (.forallE A B)
  | app : TypeRecoveryWith C Γ f (.forallE A B) →
      TypeRecoveryWith C Γ (.app f a) (B.inst a)
  | forallE : env.HasType univs Γ A (.sort u) → env.HasType univs (A :: Γ) B (.sort v) →
      TypeRecoveryWith C Γ (.forallE A B) (.sort (.imax u v))
  | proj : env.projections s info →
      TypeRecoveryWith C Γ m (mkApps (.const s ls) args) →
      info.fieldType s ls (args.take info.nparams) i m = some F →
      TypeRecoveryWith C Γ (.proj s i m) F
  | convert : TypeRecoveryWith C Γ e T → C Γ T T' →
      TypeRecoveryWith C Γ e T'

/-- Recovery certificates survive finite binder insertion, including computation
of inferred types and the universe choices in Pi formation. -/
theorem TypeRecoveryWith.weakN (hweak : ComputeWeakening C) (W : Ctx.LiftN n k Γ Γ') (R : TypeRecoveryWith C Γ e T) :
    TypeRecoveryWith C Γ' (e.liftN n k) (T.liftN n k) := by
  induction R generalizing k Γ' with
  | sort hu => exact .sort hu
  | const hc hl hn =>
    rw [((henv.ordered.closedC hc).instL).liftN_eq (Nat.zero_le _)]
    exact .const hc hl hn
  | bvar hl => exact .bvar (hl.weakN W)
  | lam _ ih => exact .lam (ih W.succ)
  | app _ ih =>
    simpa only [liftN, liftN_inst_hi] using TypeRecoveryWith.app (ih W)
  | forallE hA hB => exact .forallE (hA.weakN henv.ordered W) (hB.weakN henv.ordered W.succ)
  | @proj s info Γ m ls args i F hi _ hf ih =>
    have hclosed := henv.ordered.closedC (henv.ordered.projectionConstructor hi)
    have hf' := (VProjectionInfo.fieldType_liftN info hclosed (n := n) (k := k)
      (typeName := s) (levels := ls) (params := args.take info.nparams) (index := i) (major := m))
    rw [hf] at hf'
    simp only [Option.map_some, List.map_take] at hf'
    have hm := ih W
    simp only [liftN_mkApps, liftN] at hm
    exact TypeRecoveryWith.proj hi hm hf'
  | convert _ R ih => exact .convert (ih W) (hweak W R)

/-- A known function type retypes the argument of a well-formed application,
using ordinary uniqueness of the function's two Pi typings. -/
theorem application_at_recovered_pi (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ (.app f a))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    env.HasType univs Γ (.app f a) (B.inst a) := by
  obtain ⟨A₀, B₀, hf₀, ha⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := (hf₀.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact .app hf (hA.defeq ha)

/-- A type-recovery certificate above a binder insertion reconstructs its
entire output type below, as well as its typing. Lambda annotations come from
the source syntax; computation steps supply their own scoped result and replay. -/
theorem TypeRecoveryWith.descend_of_types (R : TypeRecoveryWith C Γ' (e.lift' ρ) T)
    (hcompute : TypeComputeDescent C)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ T₀, T = T₀.lift' ρ ∧ env.HasType univs Γ e T₀ := by
  generalize hsource : e.lift' ρ = source at R
  induction R generalizing ρ Γ e with
  | sort hu =>
    cases lift'_eq_sort hsource
    exact ⟨_, rfl, .sort hu⟩
  | const hc hl hn =>
    cases lift'_eq_const hsource
    refine ⟨_, ?_, .const hc hl hn⟩
    exact ((henv.ordered.closedC hc).instL.lift'_eq .zero).symm
  | bvar hl =>
    cases e <;> cases hsource
    obtain ⟨A, hA, hl⟩ := hl.weakU_inv W
    exact ⟨A, hA, .bvar hl⟩
  | lam _ ih =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsource
    obtain ⟨⟨u, hA⟩, hb⟩ := ht.lam_inv henv hΓ
    have hA' := hA.weak' henv.ordered W
    obtain ⟨B, rfl, hB⟩ := ih W.cons ⟨hΓ, _, hA⟩ ⟨hΓ', _, hA'⟩ hb rfl
    exact ⟨.forallE A B, rfl, .lam hA hB⟩
  | app _ ih =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsource
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨T, hT, hf⟩ := ih W hΓ hΓ' ⟨_, hf⟩ rfl
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hT.symm
    exact ⟨B.inst a, (lift'_inst_hi _ _ _).symm, application_at_recovered_pi hΓ ht hf⟩
  | forallE hAu hBv =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsource
    obtain ⟨_, ht⟩ := ht
    obtain ⟨⟨u₀, hA⟩, ⟨v₀, hB⟩⟩ := HasType.forallE_inv henv.ordered ht
    have hA' := hA.weak' henv.ordered W
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have hΓA' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ', _, hA'⟩
    have hu := (hA'.uniqU henv hΓ' hAu).sort_inv henv hΓ'
    have hv := ((hB.weak' henv.ordered W.cons).uniqU henv hΓA' hBv).sort_inv henv hΓA'
    have hAu₀ := (IsDefEq.sortDF (hA.sort_r henv hΓ) (hAu.sort_r henv hΓ') hu).defeq hA
    have hBv₀ := (IsDefEq.sortDF (hB.sort_r henv hΓA)
      (hBv.sort_r henv hΓA') hv).defeq hB
    exact ⟨_, rfl, .forallE hAu₀ hBv₀⟩
  | proj hi _ hf ih =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsource
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    obtain ⟨T, hT, hm⟩ := ih W hΓ hΓ' ⟨_, hm.hasType.2⟩ rfl
    obtain ⟨args, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine hT.symm
    rw [← List.map_take] at hf
    have hclosed := henv.ordered.closedC (henv.ordered.projectionConstructor hi)
    obtain ⟨F, hF, hf⟩ := fieldType_lift'_inv hclosed hf
    exact ⟨F, hF, projection_at_recovered_family henv hΓ hi ⟨_, ht'⟩ hm hf⟩
  | convert _ R ih =>
    obtain ⟨T, rfl, heT⟩ := ih W hΓ hΓ' ht hsource
    obtain ⟨u, hT⟩ := heT.isType henv hΓ
    obtain ⟨T', hT', H⟩ := hcompute R W hΓ hΓ' hT
    exact ⟨T', hT', H.defeq heT⟩

/-- Ordinary computation descent is a sufficient special case of the weaker
type-only interface used by the recovery induction. -/
theorem TypeRecoveryWith.descend (R : TypeRecoveryWith C Γ' (e.lift' ρ) T)
    (hcompute : ComputeDescent C)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ T₀, T = T₀.lift' ρ ∧ env.HasType univs Γ e T₀ :=
  R.descend_of_types hcompute.types W hΓ hΓ' ht

/-- Sort-typed computational replay already suffices for ambient recovery. -/
theorem TypeRecoveryWith.hasType_of_types (R : TypeRecoveryWith C Γ e T)
    (hc : TypeComputeDescent C) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ e) : env.HasType univs Γ e T := by
  have R' : TypeRecoveryWith C Γ (e.lift' .refl) T := by simpa using R
  obtain ⟨T₀, hT, H⟩ := R'.descend_of_types hc .refl hΓ hΓ ht
  simp only [lift'_refl] at hT
  exact hT.symm ▸ H

/-- A recovered Pi typing determines scoped eta annotations below. -/
theorem TypeRecoveryWith.pi_below (R : TypeRecoveryWith C Γ' (e.lift' ρ) (.forallE A B))
    (hcompute : ComputeDescent C)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ A₀ B₀, A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons ∧ env.HasType univs Γ e (.forallE A₀ B₀) := by
  obtain ⟨T, hT, ht⟩ := R.descend hcompute W hΓ hΓ' ht
  obtain ⟨A₀, B₀, rfl, hA, hB⟩ := lift'_eq_forallE hT.symm
  exact ⟨A₀, B₀, hA, hB, ht⟩

/-- Enlarging the allowed computation enlarges recovery, including conversions
nested under applications, binders and projection majors. -/
theorem TypeRecoveryWith.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (R : TypeRecoveryWith C Γ e T) : TypeRecoveryWith C' Γ e T := by
  induction R with
  | sort h => exact .sort h
  | const hc hl hn => exact .const hc hl hn
  | bvar h => exact .bvar h
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih
  | forallE hA hB => exact .forallE hA hB
  | proj hi _ hf ih => exact .proj hi ih hf
  | convert _ H ih => exact .convert ih (hC H)

/-- Source well-formedness suffices to reconstruct the chosen type. -/
theorem TypeRecoveryWith.hasType (R : TypeRecoveryWith C Γ e T)
    (hc : ComputeDescent C) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ e) : env.HasType univs Γ e T := by
  have R' : TypeRecoveryWith C Γ (e.lift' .refl) T := by simpa using R
  obtain ⟨T₀, hT, H⟩ := R'.descend hc .refl hΓ hΓ ht
  simp only [lift'_refl] at hT
  exact hT.symm ▸ H

end Lean4Lean.VEnv.Strengthening
