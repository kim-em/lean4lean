import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongVariableTrace

/-! # Finite bounds on actual strong derivations

Every original strong premise is retained at a strictly smaller numeric rank.
A strict rank-raising rule permits finite maxima without assigning a computable
height to a Prop-valued derivation. The bound is existential, not normalization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

section
set_option hygiene false
variable (env : VEnv) (uvars : Nat)
local notation:65 Γ " ⊢ " e " : " A:30 => StrongBounded n Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => StrongBounded n Γ e1 e2 A
local notation:65 Γ " ⊣ " e " : " A:30 => StrongBounded (n+1) Γ e e A
local notation:65 Γ " ⊣ " e1 " ≡ " e2 " : " A:30 => StrongBounded (n+1) Γ e1 e2 A

/-- The full strong grammar with strict premise ranks. Rank raising is strict,
so it also permits induction on the numeric index. Pattern checks share a finite
bound because their realized list is finite. No equality constructor is omitted. -/
inductive StrongBounded : Nat → List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊣ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊣ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊣ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊣ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊣ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊣ .app f a ≡ .app f' a' : B.inst a
  | projDF :
    env.projections typeName info →
    (∀ l ∈ levels, l.WF uvars) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    fieldLevel.WF uvars →
    Γ ⊢ fieldType : .sort fieldLevel →
    Γ ⊢ sourceMajor ≡ major :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    Γ ⊢ sourceMajor ≡ major' :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    info.ctorType.Closed →
    (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero →
    Γ ⊣ .proj typeName index major ≡
      .proj typeName index major' : fieldType
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊣ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊣ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊣ e1 ≡ e2 : B
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ B.inst e' : .sort v →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊣ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A.lift::A::Γ ⊢ B.liftN 1 1 : .sort v →
    Γ ⊢ e : .forallE A B →
    A::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) →
    A::Γ ⊢ A.lift : .sort u →
    Γ ⊣ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊣ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls →
    [] ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊣ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  /-- As `IsDefEq.pat`, whose reduct-typing premise it carries strongly. -/
  | pat {p : Pattern} {r : p.RHS × p.Check} {m1 m2 chk} :
    env.pats p r → p.Matches e m1 m2 → Γ ⊢ e : A →
    Γ ⊢ r.1.apply m1 m2 : A →
    r.2.Realizes m1 m2 chk →
    (∀ t ∈ chk, Γ ⊢ t.1 ≡ t.2.1 : t.2.2) →
    Γ ⊣ e ≡ r.1.apply m1 m2 : A
  | projIota :
    env.projections typeName info →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType →
    args[info.nparams + index]? = some field →
    Γ ⊢ field : fieldType →
    Γ ⊣ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) ≡ field :
      fieldType
  | structEta :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) :
      VExpr.mkApps (.const typeName levels) params →
    Γ ⊣ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) ≡ e :
      VExpr.mkApps (.const typeName levels) params
  | unitLike :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    info.numFields = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e' : VExpr.mkApps (.const typeName levels) params →
    Γ ⊣ e ≡ e' : VExpr.mkApps (.const typeName levels) params

  | raise (hlt : n < m) : StrongBounded n Γ a b A → StrongBounded m Γ a b A

end

/-- Raising a bound preserves the derivation; equality of bounds is reflexive. -/
theorem StrongBounded.mono (H : StrongBounded env U n Γ a b A) (hle : n ≤ m) :
    StrongBounded env U m Γ a b A := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact H
  · exact .raise hlt H

variable! (henv : Ordered env) in
/-- Ordinary weakening preserves the exact derivation bound. Every original
premise remains at its old rank, including the finite family of pattern checks.
This does not assert a bound for substitution or conversion of the context. -/
theorem StrongBounded.weakN (W : Ctx.LiftN n k Γ Γ') (H : StrongBounded env U rank Γ e1 e2 A) :
    StrongBounded env U rank Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 h2 _ ih3 => refine .bvar (h1.weakN W) h2 (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 (ih2 W)
  | pat hp hm _ _ hr _ ihe ihred ihall =>
    have ihred := ihred W
    rw [Pattern.RHS.liftN_apply] at ihred ⊢
    refine .pat hp (Pattern.matches_liftN.2 ⟨_, hm, fun _ => rfl⟩) (ihe W) ihred hr.map_liftN ?_
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    exact ihall t0 ht0 W
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine liftN_inst_hi .. ▸ .appDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W) (ih4 W) ?_
    exact liftN_inst_hi .. ▸ liftN_inst_hi .. ▸ ih5 W
  | @projDF typeName info levels params index sourceMajor fieldType _ _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_liftN
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (n := n) (k := k) info hclosed
    rw [hfield] at hfield'
    have hleft := ihLeft W
    have hright := ihRight W
    simp only [VExpr.liftN_mkApps, List.map_append, VExpr.liftN] at hleft hright
    simpa [VExpr.liftN] using
      (.projDF (info := info) (params := params.map fun param => param.liftN n k)
        (indexArgs := indexArgs.map fun arg => arg.liftN n k)
        hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
        hfield' hwf (ihField W) hleft hright hclosed hguard)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta h1 h2
      (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
      (liftN_instN_hi .. ▸ ih5 W :)
      (liftN_instN_hi .. ▸ liftN_instN_hi .. ▸ ih6 W :)
  | @eta _ Γ a u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have := StrongBounded.eta h1 h2 (ih1 W) (ih2 W.succ) ?_ (ih4 W) ?_ ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W.succ.succ
      have := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
      rw [Nat.add_comm 1] at this; rwa [← this, ← lift_liftN'] at ih3
    · have ih5 : StrongBounded _ _ _ _ _ _ (liftN n (lift (forallE ..)) _) := ih5 W.succ
      rwa [← lift_liftN', ← lift_liftN'] at ih5
    · have ih6 := ih6 W.succ
      rwa [← lift_liftN'] at ih6
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact StrongBounded.extra h1 h2 h3 h4 h5 h6 h7 (ih4 W) (ih5 W)
  | projIota h1 _ h3 _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at ih1 ⊢
    exact .projIota h1 ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def] at ih1 ih2 ⊢
    exact .structEta h1 (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at ih1 ih2 ⊢
    exact .unitLike h1 (by simpa using h2) h3 h4 ih1 ih2

  | raise hlt H ih => exact .raise hlt (ih W)

/-- Forgetting ranks gives exactly an original strong derivation. -/
theorem StrongBounded.strong (H : StrongBounded env U n Γ a b A) :
    env.IsDefEqStrong U Γ a b A := by
  induction H with
  | bvar h1 h2 _ ih => exact .bvar h1 h2 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih ih' => exact .constDF h1 h2 h3 h4 h5 h6 ih ih'
  | appDF h1 h2 _ _ _ _ _ i1 i2 i3 i4 i5 => exact .appDF h1 h2 i1 i2 i3 i4 i5
  | projDF h1 h2 h3 h4 h5 h6 h7 _ _ _ h8 h9 i1 i2 i3 =>
    exact .projDF h1 h2 h3 h4 h5 h6 h7 i1 i2 i3 h8 h9
  | lamDF h1 h2 _ _ _ _ _ i1 i2 i3 i4 i5 => exact .lamDF h1 h2 i1 i2 i3 i4 i5
  | forallEDF h1 h2 _ _ _ i1 i2 i3 => exact .forallEDF h1 h2 i1 i2 i3
  | defeqDF h1 _ _ i1 i2 => exact .defeqDF h1 i1 i2
  | beta h1 h2 _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 => exact .beta h1 h2 i1 i2 i3 i4 i5 i6
  | eta h1 h2 _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 => exact .eta h1 h2 i1 i2 i3 i4 i5 i6
  | proofIrrel _ _ _ i1 i2 i3 => exact .proofIrrel i1 i2 i3
  | extra h1 h2 h3 h4 _ _ _ _ _ i1 i2 i3 i4 i5 => exact .extra h1 h2 h3 h4 i1 i2 i3 i4 i5
  | pat h1 h2 _ _ h3 _ i1 i2 i3 => exact .pat h1 h2 i1 i2 h3 i3
  | projIota h1 _ h2 _ i1 i2 => exact .projIota h1 i1 h2 i2
  | structEta h1 h2 h3 _ _ i1 i2 => exact .structEta h1 h2 h3 i1 i2
  | unitLike h1 h2 h3 h4 _ _ i1 i2 => exact .unitLike h1 h2 h3 h4 i1 i2
  | raise _ _ ih => exact ih


private theorem finite_checks {checks : List (VExpr × VExpr × VExpr)}
    (H : ∀ t ∈ checks, ∃ n, StrongBounded env U n Γ t.1 t.2.1 t.2.2) :
    ∃ n, ∀ t ∈ checks, StrongBounded env U n Γ t.1 t.2.1 t.2.2 := by
  induction checks with
  | nil => exact ⟨0, by simp⟩
  | cons t ts ih =>
    obtain ⟨n, ht⟩ := H t (by simp)
    obtain ⟨m, hs⟩ := ih (fun x hx => H x (by simp [hx]))
    refine ⟨max n m, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ht.mono (Nat.le_max_left _ _)
    · exact (hs x hx).mono (Nat.le_max_right _ _)

/-- Every original strong derivation has some finite bound. Each actual rule
raises a common bound on all its premises. The pattern rule uses finiteness of
its realized check list, not a uniform bound on an arbitrary infinite family. -/
theorem strong_has_bound (H : env.IsDefEqStrong U Γ a b A) :
    ∃ n, StrongBounded env U n Γ a b A := by
  induction H with
  | bvar h1 h2 _ i1 =>
    obtain ⟨n1, H1⟩ := i1
    exact ⟨(n1)+1, .bvar h1 h2 (H1.mono (by omega))⟩
  | symm _ i1 =>
    obtain ⟨n1, H1⟩ := i1
    exact ⟨(n1)+1, .symm (H1.mono (by omega))⟩
  | trans _ _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .trans (H1.mono (by omega)) (H2.mono (by omega))⟩
  | sortDF h1 h2 h3 =>
    exact ⟨(0)+1, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 h6 _ _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .constDF h1 h2 h3 h4 h5 h6 (H1.mono (by omega)) (H2.mono (by omega))⟩
  | appDF h1 h2 _ _ _ _ _ i1 i2 i3 i4 i5 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    obtain ⟨n4, H4⟩ := i4
    obtain ⟨n5, H5⟩ := i5
    exact ⟨(n1+n2+n3+n4+n5)+1, .appDF h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) (H4.mono (by omega)) (H5.mono (by omega))⟩
  | projDF h1 h2 h3 h4 h5 h6 h7 _ _ _ h8 h9 i1 i2 i3 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    exact ⟨(n1+n2+n3)+1, .projDF h1 h2 h3 h4 h5 h6 h7 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) h8 h9⟩
  | lamDF h1 h2 _ _ _ _ _ i1 i2 i3 i4 i5 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    obtain ⟨n4, H4⟩ := i4
    obtain ⟨n5, H5⟩ := i5
    exact ⟨(n1+n2+n3+n4+n5)+1, .lamDF h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) (H4.mono (by omega)) (H5.mono (by omega))⟩
  | forallEDF h1 h2 _ _ _ i1 i2 i3 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    exact ⟨(n1+n2+n3)+1, .forallEDF h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega))⟩
  | defeqDF h1 _ _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .defeqDF h1 (H1.mono (by omega)) (H2.mono (by omega))⟩
  | beta h1 h2 _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    obtain ⟨n4, H4⟩ := i4
    obtain ⟨n5, H5⟩ := i5
    obtain ⟨n6, H6⟩ := i6
    exact ⟨(n1+n2+n3+n4+n5+n6)+1, .beta h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) (H4.mono (by omega)) (H5.mono (by omega)) (H6.mono (by omega))⟩
  | eta h1 h2 _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    obtain ⟨n4, H4⟩ := i4
    obtain ⟨n5, H5⟩ := i5
    obtain ⟨n6, H6⟩ := i6
    exact ⟨(n1+n2+n3+n4+n5+n6)+1, .eta h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) (H4.mono (by omega)) (H5.mono (by omega)) (H6.mono (by omega))⟩
  | proofIrrel _ _ _ i1 i2 i3 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    exact ⟨(n1+n2+n3)+1, .proofIrrel (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega))⟩
  | extra h1 h2 h3 h4 _ _ _ _ _ i1 i2 i3 i4 i5 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := i3
    obtain ⟨n4, H4⟩ := i4
    obtain ⟨n5, H5⟩ := i5
    exact ⟨(n1+n2+n3+n4+n5)+1, .extra h1 h2 h3 h4 (H1.mono (by omega)) (H2.mono (by omega)) (H3.mono (by omega)) (H4.mono (by omega)) (H5.mono (by omega))⟩
  | projIota h1 _ h2 _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .projIota h1 (H1.mono (by omega)) h2 (H2.mono (by omega))⟩
  | structEta h1 h2 h3 _ _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .structEta h1 h2 h3 (H1.mono (by omega)) (H2.mono (by omega))⟩
  | unitLike h1 h2 h3 h4 _ _ i1 i2 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    exact ⟨(n1+n2)+1, .unitLike h1 h2 h3 h4 (H1.mono (by omega)) (H2.mono (by omega))⟩
  | pat h1 h2 _ _ h3 _ i1 i2 i3 =>
    obtain ⟨n1, H1⟩ := i1
    obtain ⟨n2, H2⟩ := i2
    obtain ⟨n3, H3⟩ := finite_checks i3
    exact ⟨(n1+n2+n3)+1, .pat h1 h2 (H1.mono (by omega)) (H2.mono (by omega)) h3
      (fun t ht => (H3 t ht).mono (by omega))⟩

/-- Existential finite rank is exactly the original strong judgment. This
changes the induction interface without restricting the calculus. -/
theorem strong_iff_bounded : env.IsDefEqStrong U Γ a b A ↔
    ∃ n, StrongBounded env U n Γ a b A :=
  ⟨strong_has_bound, fun ⟨_, H⟩ => H.strong⟩


/-- Every conversion edge has a strong derivation strictly below the retained
parent bound. The trace keeps each edge's own rank rather than replacing it by
a new composed strong equality. -/
inductive BoundedTypeTrace (env : VEnv) (U bound : Nat) (Γ : List VExpr) :
    VExpr → VExpr → Prop where
  | refl : BoundedTypeTrace env U bound Γ A A
  | step (hlt : k < bound) : BoundedTypeTrace env U bound Γ A B →
      StrongBounded env U k Γ B C (.sort u) → BoundedTypeTrace env U bound Γ A C

/-- Increasing the parent bound leaves all recorded edge ranks unchanged. -/
theorem BoundedTypeTrace.mono (H : BoundedTypeTrace env U n Γ A B) (hle : n ≤ m) :
    BoundedTypeTrace env U m Γ A B := by
  induction H with
  | refl => exact .refl
  | step hlt H HE ih => exact .step (Nat.lt_of_lt_of_le hlt hle) ih HE

private def BoundedVariableAssignment (env : VEnv) (U n : Nat)
    (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∀ i, e = .bvar i → ∃ B, Lookup Γ i B ∧ BoundedTypeTrace env U n Γ B A

private theorem BoundedVariableAssignment.mono
    (H : BoundedVariableAssignment env U n Γ e A) (hle : n ≤ m) :
    BoundedVariableAssignment env U m Γ e A := by
  intro i E
  obtain ⟨B, hl, H⟩ := H i E
  exact ⟨B, hl, H.mono hle⟩

private theorem BoundedVariableAssignment.convert
    (H : BoundedVariableAssignment env U n Γ e A)
    (HT : StrongBounded env U n Γ A B (.sort u)) :
    BoundedVariableAssignment env U (n+1) Γ e B := by
  intro i E
  obtain ⟨C, hl, H⟩ := H i E
  exact ⟨C, hl, .step (Nat.lt_succ_self n) (H.mono (Nat.le_succ n)) HT⟩

private theorem bounded_variable_assignment
    (H : StrongBounded env U n Γ a b A) :
    BoundedVariableAssignment env U n Γ a A ∧ BoundedVariableAssignment env U n Γ b A := by
  induction H with
  | bvar hl hu hA =>
    constructor <;> intro i E <;> cases E <;> exact ⟨_, hl, .refl⟩
  | symm _ ih => exact ⟨ih.2.mono (Nat.le_succ _), ih.1.mono (Nat.le_succ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.mono (Nat.le_succ _), ih₂.2.mono (Nat.le_succ _)⟩
  | sortDF | constDF | appDF | projDF | lamDF | forallEDF =>
    constructor <;> intro i E <;> cases E
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.convert HT, ih.2.convert HT⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih8 =>
    exact ⟨(fun i E => by cases E), ih8.1.mono (Nat.le_succ _)⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun i E => by cases E), ih6.1.mono (Nat.le_succ _)⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨ih2.1.mono (Nat.le_succ _), ih3.1.mono (Nat.le_succ _)⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact ⟨ih8.1.mono (Nat.le_succ _), ih9.1.mono (Nat.le_succ _)⟩
  | pat hp hm he hred hr hall ihe ihred ihall =>
    exact ⟨ihe.1.mono (Nat.le_succ _), ihred.1.mono (Nat.le_succ _)⟩
  | projIota hi ht hg hf iht ihf =>
    exact ⟨iht.1.mono (Nat.le_succ _), ihf.1.mono (Nat.le_succ _)⟩
  | structEta hi hp hx hm hc ihm ihc =>
    exact ⟨ihc.1.mono (Nat.le_succ _), ihm.1.mono (Nat.le_succ _)⟩
  | unitLike hi hp hx hz hm hn ihm ihn =>
    exact ⟨ihm.1.mono (Nat.le_succ _), ihn.1.mono (Nat.le_succ _)⟩
  | raise hlt H ih => exact ⟨ih.1.mono (Nat.le_of_lt hlt), ih.2.mono (Nat.le_of_lt hlt)⟩

/-- The native assignment path for either variable endpoint has only strictly
lower-rank type-conversion edges. Every constructor, including rank raising and
realized pattern checks, participates in the same induction. -/
theorem StrongBounded.variable_assignment_trace
    (H : StrongBounded env U n Γ a b A) (HE : a = .bvar i ∨ b = .bvar i) :
    ∃ B, Lookup Γ i B ∧ BoundedTypeTrace env U n Γ B A :=
  HE.elim (fun E => (bounded_variable_assignment H).1 i E)
    (fun E => (bounded_variable_assignment H).2 i E)

/-- Lookup uniqueness fixes the native starting type without synthesizing a
new conversion derivation or increasing any edge's rank. -/
theorem StrongBounded.variable_native_trace
    (H : StrongBounded env U n Γ (.bvar i) (.bvar i) A) (hl : Lookup Γ i B) :
    BoundedTypeTrace env U n Γ B A := by
  obtain ⟨C, hc, R⟩ := H.variable_assignment_trace (.inl rfl)
  cases hl.uniq hc
  exact R

/-- An original strong derivation admits a finite ranked realization and a
native-variable trace strictly below that same bound. This is an existential
bound on derivations, not a proof-height function on Prop witnesses. -/
theorem strong_variable_has_bounded_trace
    (H : env.IsDefEqStrong U Γ a b A) (HE : a = .bvar i ∨ b = .bvar i) :
    ∃ n, StrongBounded env U n Γ a b A ∧
      ∃ B, Lookup Γ i B ∧ BoundedTypeTrace env U n Γ B A := by
  obtain ⟨n, Hn⟩ := strong_has_bound H
  exact ⟨n, Hn, Hn.variable_assignment_trace HE⟩

/-- Numeric strong induction may interpret each retained edge using its
strictly smaller rank. This proves the local recursion interface; the edge
handler itself and bounds for new substitution/composition cuts remain open. -/
theorem BoundedTypeTrace.pullback (H : BoundedTypeTrace env U n Γ A B)
    (P : VExpr → Prop)
    (edge : ∀ {k X Y u}, k < n → StrongBounded env U k Γ X Y (.sort u) → P Y → P X)
    (HB : P B) : P A := by
  induction H with
  | refl => exact HB
  | step hlt H HE ih => exact ih (edge hlt HE HB)

/-- The local induction hypothesis need only cover ranks below the variable's
actual strong bound. It can then return an assigned-carrier property to the
native lookup type. No blanket unranked conversion law is used by this fold. -/
theorem StrongBounded.variable_native_pullback
    (H : StrongBounded env U n Γ (.bvar i) (.bvar i) A) (hl : Lookup Γ i B)
    (P : VExpr → Prop)
    (edge : ∀ {k X Y u}, k < n → StrongBounded env U k Γ X Y (.sort u) → P Y → P X)
    (HA : P A) : P B :=
  (H.variable_native_trace hl).pullback P edge HA


/-- Weakening the whole conversion trace preserves its parent bound and every
strict edge bound. An induction hypothesis generalized over contexts can thus
consume the weakened type children at their original ranks. -/
theorem BoundedTypeTrace.weakN (henv : Ordered env)
    (W : Ctx.LiftN count offset Γ Γ') (H : BoundedTypeTrace env U n Γ A B) :
    BoundedTypeTrace env U n Γ' (A.liftN count offset) (B.liftN count offset) := by
  induction H with
  | refl => exact .refl
  | step hlt H HE ih => exact .step hlt ih (HE.weakN henv W)

open Params in
/-- Forgetting numeric bounds recovers the previous finite trace. -/
theorem BoundedTypeTrace.forget [Params]
    (H : BoundedTypeTrace env univs n Γ A B) : StrongTypeTrace Γ A B := by
  induction H with
  | refl => exact .refl
  | step hlt H HE ih => exact ih.step HE.strong

end Lean4Lean.VEnv.Strengthening
