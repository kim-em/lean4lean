import Lean4Lean.Theory.Typing.Strengthening.CertifiedKSubstitution

/-! # Applying recursive certificates through displayed beta redexes

A hybrid comparison in function position cannot always be used as an application
comparison. Contracting its displayed lambda cases instead gives a certified
join when the arguments have a recursive domain comparison. This supports eta
at the function and computational endpoint alignment without normalizing loops.
Arbitrary hybrid argument comparisons are not assumed to satisfy this premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

private theorem argument_at_other_domain (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hf' : env.HasType univs Γ f (.forallE D C))
    (hx : env.HasType univs Γ x A) : env.HasType univs Γ x D := by
  obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
  exact hAD.defeq hx

private theorem beta_compute :
    CertifiedKCompute D depth Γ (.app (.lam A b) x) (b.inst x) :=
  .base (.base (.base (.base .beta)))

/-- Applying a hybrid function comparison to domain-certified arguments yields
a finite computational join. Eta cases instantiate their body comparisons;
displayed lambdas contract instead of requiring an independent function guard. -/
theorem HybridNormal.apply_domain_arg (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : HybridNormal n Γ f g) (Harg : DomainNormal m Γ x y) :
    KCertificate D (depth + 1) Γ (.app f x) (.app g y) := by
  obtain ⟨_, Harg'⟩ := Harg.toHybrid hΓ
  cases H with
  | refl _ =>
    exact KCertificate.normal (.appDF (.inr ⟨0, .refl hf⟩) hf hg hx hy (.refl hf) Harg')
  | sortDF h1 h2 h3 =>
    exact KCertificate.normal (.appDF (.inl ⟨by simp [IsLam], by simp [IsLam]⟩) hf hg hx hy
      (.sortDF h1 h2 h3) Harg')
  | constDF h1 h2 h3 h4 h5 =>
    exact KCertificate.normal (.appDF (.inl ⟨by simp [IsLam], by simp [IsLam]⟩) hf hg hx hy
      (.constDF h1 h2 h3 h4 h5) Harg')
  | appDF hside h1 h2 h3 h4 Hf Ha =>
    exact KCertificate.normal (.appDF (.inl ⟨by simp [IsLam], by simp [IsLam]⟩) hf hg hx hy
      (.appDF hside h1 h2 h3 h4 Hf Ha) Harg')
  | projDF hp Hm =>
    exact KCertificate.normal (.appDF (.inl ⟨by simp [IsLam], by simp [IsLam]⟩) hf hg hx hy
      (.projDF hp Hm) Harg')
  | forallEDF h1 HA h3 HB =>
    exact KCertificate.normal (.appDF (.inl ⟨by simp [IsLam], by simp [IsLam]⟩) hf hg hx hy
      (.forallEDF h1 HA h3 HB) Harg')
  | lamDF hD1 _ HB =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    obtain ⟨_, hb⟩ := HB.defeq hΓD
    have hfD := (IsDefEq.lamDF hD1 hb.hasType.1).hasType.2
    have hxD := argument_at_other_domain hΓ hf hfD hx
    obtain ⟨j, H'⟩ := HB.instN_lr hΓD hxD Harg .zero
    exact ⟨_, _, j, beta_compute, beta_compute, H'⟩
  | etaL hgD HB =>
    have hxD := argument_at_other_domain hΓ hg hgD hx
    obtain ⟨_, hD⟩ := hxD.isType henv hΓ
    have hΓD : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    obtain ⟨j, H'⟩ := HB.instN_lr hΓD hxD Harg .zero
    simp only [inst, instVar_zero, inst_lift] at H'
    exact ⟨_, _, j, beta_compute, .base .refl, H'⟩
  | etaR hfD HB =>
    have hxD := argument_at_other_domain hΓ hf hfD hx
    obtain ⟨_, hD⟩ := hxD.isType henv hΓ
    have hΓD : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    obtain ⟨j, H'⟩ := HB.instN_lr hΓD hxD Harg .zero
    simp only [inst, instVar_zero, inst_lift] at H'
    exact ⟨_, _, j, .base .refl, beta_compute, H'⟩
  | etaBoth hfD _ HB =>
    have hxD := argument_at_other_domain hΓ hf hfD hx
    obtain ⟨_, hD⟩ := hxD.isType henv hΓ
    have hΓD : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    obtain ⟨j, H'⟩ := HB.instN_lr hΓD hxD Harg .zero
    simp only [inst, instVar_zero, inst_lift] at H'
    exact ⟨_, _, j, .base .refl, .base .refl, H'⟩
  | proofIrrel hp hfp hgp =>
    obtain ⟨Q, hfx, hQ⟩ := IsProof.app_fn hΓ hf hx ⟨_, hfp, hp⟩
    have E := IsDefEq.appDF
      ((show env.IsDefEqU univs Γ _ _ from ⟨_, .proofIrrel hp hfp hgp⟩).of_l henv hΓ hf)
      ((Harg.defeq hΓ).of_l henv hΓ hx)
    have hgy := (IsDefEq.trans_l henv hΓ hfx E).hasType.2
    exact KCertificate.normal (.proofIrrel hQ hfx hgy)

/-- Prepending compatible computations preserves a positive-depth certificate. -/
theorem KCertificate.prepend (Ra : CertifiedKCompute D depth Γ a a')
    (Rb : CertifiedKCompute D depth Γ b b') (H : KCertificate D (depth + 1) Γ a' b') :
    KCertificate D (depth + 1) Γ a b := by
  obtain ⟨a'', b'', n, Ra', Rb', H⟩ := H
  exact ⟨a'', b'', n, Ra.trans Ra', Rb.trans Rb', H⟩

/-- Computationally certified functions can be applied to domain-certified
arguments at the same positive certificate depth. Intermediate function types
are recovered by source replay, including nested K computations. -/
theorem KCertificate.apply_domain_arg (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : KCertificate D (depth + 1) Γ f g) (Harg : DomainNormal m Γ x y) :
    KCertificate D (depth + 1) Γ (.app f x) (.app g y) := by
  obtain ⟨f', g', n, Rf, Rg, H⟩ := H
  have hf' := (Rf.simAt heq hs (KCertificate.descends heq hs depth) hΓ _ hf).hasType.2
  have hg' := (Rg.simAt heq hs (KCertificate.descends heq hs depth) hΓ _ hg).hasType.2
  exact (H.apply_domain_arg hΓ hf' hg' hx hy Harg).prepend
    (.app Rf (.base .refl)) (.app Rg (.base .refl))

/-- Arguments may first compute through nested K steps to a domain-certified
pair. Their reduct typings are obtained from replay, so the argument certificate
need not be present at the original syntax. -/
theorem KCertificate.apply_computed_domain_args
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : KCertificate D (depth + 1) Γ f g)
    (Rx : CertifiedKCompute D depth Γ x x') (Ry : CertifiedKCompute D depth Γ y y')
    (Harg : DomainNormal m Γ x' y') :
    KCertificate D (depth + 1) Γ (.app f x) (.app g y) := by
  have hx' := (Rx.simAt heq hs (KCertificate.descends heq hs depth) hΓ _ hx).hasType.2
  have hy' := (Ry.simAt heq hs (KCertificate.descends heq hs depth) hΓ _ hy).hasType.2
  exact (H.apply_domain_arg heq hs hΓ hf hg hx' hy' Harg).prepend
    (.app (.base .refl) Rx) (.app (.base .refl) Ry)

/-- In particular, no special annotation certificate is required for a shared
argument: its recursive comparison is reflexive, even when it is a lambda. -/
theorem KCertificate.apply_same_arg (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (H : KCertificate D (depth + 1) Γ f g) :
    KCertificate D (depth + 1) Γ (.app f x) (.app g x) :=
  H.apply_domain_arg heq hs hΓ hf hg hx hx (.refl hx)

end Lean4Lean.VEnv.Strengthening
