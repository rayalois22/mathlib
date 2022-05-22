/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.adjoin.basic
import linear_algebra.linear_independent
import ring_theory.mv_polynomial.basic
import data.mv_polynomial.supported
import ring_theory.algebraic
import data.mv_polynomial.equiv
/-!
# Algebraic Independence

This file defines algebraic independence of a family of element of an `R` algebra

## Main definitions

* `algebraic_independent` - `algebraic_independent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical map out of the multivariable
  polynomial ring is injective.

* `algebraic_independent.repr` - The canonical map from the subalgebra generated by an
  algebraic independent family into the polynomial ring.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## TODO
Prove that a ring is an algebraic extension of the subalgebra generated by a transcendence basis.

## Tags
transcendence basis, transcendence degree, transcendence

-/
noncomputable theory

open function set subalgebra mv_polynomial algebra
open_locale classical big_operators

universes x u v w

variables {ι : Type*} {ι' : Type*} (R : Type*) {K : Type*}
variables {A : Type*} {A' A'' : Type*} {V : Type u} {V' : Type*}
variables (x : ι → A)
variables [comm_ring R] [comm_ring A] [comm_ring A'] [comm_ring A'']
variables [algebra R A] [algebra R A'] [algebra R A'']
variables {a b : R}

/-- `algebraic_independent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical
  map out of the multivariable polynomial ring is injective. -/
def algebraic_independent : Prop :=
injective (mv_polynomial.aeval x : mv_polynomial ι R →ₐ[R] A)

variables {R} {x}

theorem algebraic_independent_iff_ker_eq_bot : algebraic_independent R x ↔
  (mv_polynomial.aeval x : mv_polynomial ι R →ₐ[R] A).to_ring_hom.ker = ⊥ :=
ring_hom.injective_iff_ker_eq_bot _

theorem algebraic_independent_iff : algebraic_independent R x ↔
  ∀p : mv_polynomial ι R, mv_polynomial.aeval (x : ι → A) p = 0 → p = 0 :=
injective_iff_map_eq_zero _

theorem algebraic_independent.eq_zero_of_aeval_eq_zero (h : algebraic_independent R x) :
  ∀p : mv_polynomial ι R, mv_polynomial.aeval (x : ι → A) p = 0 → p = 0 :=
algebraic_independent_iff.1 h

theorem algebraic_independent_iff_injective_aeval :
  algebraic_independent R x ↔ injective (mv_polynomial.aeval x : mv_polynomial ι R →ₐ[R] A) :=
iff.rfl

@[simp] lemma algebraic_independent_empty_type_iff [is_empty ι] :
  algebraic_independent R x ↔ injective (algebra_map R A) :=
have aeval x = (algebra.of_id R A).comp (@is_empty_alg_equiv R ι _ _).to_alg_hom,
  by { ext i, exact is_empty.elim' ‹is_empty ι› i },
begin
  rw [algebraic_independent, this,
    ← injective.of_comp_iff' _ (@is_empty_alg_equiv R ι _ _).bijective],
  refl
end

namespace algebraic_independent

variables (hx : algebraic_independent R x)

include hx

lemma algebra_map_injective : injective (algebra_map R A) :=
by simpa [← mv_polynomial.algebra_map_eq, function.comp] using
    (injective.of_comp_iff
      (algebraic_independent_iff_injective_aeval.1 hx) (mv_polynomial.C)).2
    (mv_polynomial.C_injective _ _)

lemma linear_independent : linear_independent R x :=
begin
  rw [linear_independent_iff_injective_total],
  have : finsupp.total ι A R x =
    (mv_polynomial.aeval x).to_linear_map.comp (finsupp.total ι _ R X),
  { ext, simp },
  rw this,
  refine hx.comp _,
  rw [← linear_independent_iff_injective_total],
  exact linear_independent_X _ _
end

protected lemma injective [nontrivial R] : injective x :=
hx.linear_independent.injective

lemma ne_zero [nontrivial R] (i : ι) : x i ≠ 0 :=
hx.linear_independent.ne_zero i

lemma comp (f : ι' → ι) (hf : function.injective f) : algebraic_independent R (x ∘ f) :=
λ p q, by simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hx (rename f p) (rename f q)

lemma coe_range : algebraic_independent R (coe : range x → A) :=
by simpa using hx.comp _ (range_splitting_injective x)

lemma map {f : A →ₐ[R] A'} (hf_inj : set.inj_on f (adjoin R (range x))) :
  algebraic_independent R (f ∘ x) :=
have aeval (f ∘ x) = f.comp (aeval x), by ext; simp,
have h : ∀ p : mv_polynomial ι R, aeval x p ∈ (@aeval R _ _ _ _ _ (coe : range x → A)).range,
  { intro p,
    rw [alg_hom.mem_range],
    refine ⟨mv_polynomial.rename (cod_restrict x (range x) (mem_range_self)) p, _⟩,
    simp [function.comp, aeval_rename] },
begin
  intros x y hxy,
  rw [this] at hxy,
  rw [adjoin_eq_range] at hf_inj,
  exact hx (hf_inj (h x) (h y) hxy)
end

lemma map' {f : A →ₐ[R] A'} (hf_inj : injective f) : algebraic_independent R (f ∘ x) :=
hx.map (inj_on_of_injective hf_inj _)

omit hx

lemma of_comp (f : A →ₐ[R] A') (hfv : algebraic_independent R (f ∘ x)) :
  algebraic_independent R x :=
have aeval (f ∘ x) = f.comp (aeval x), by ext; simp,
by rw [algebraic_independent, this] at hfv; exact hfv.of_comp

end algebraic_independent

open algebraic_independent

lemma alg_hom.algebraic_independent_iff (f : A →ₐ[R] A') (hf : injective f) :
  algebraic_independent R (f ∘ x) ↔ algebraic_independent R x :=
⟨λ h, h.of_comp f, λ h, h.map (inj_on_of_injective hf _)⟩

@[nontriviality]
lemma algebraic_independent_of_subsingleton [subsingleton R] : algebraic_independent R x :=
by haveI := @mv_polynomial.unique R ι;
  exact algebraic_independent_iff.2 (λ l hl, subsingleton.elim _ _)

theorem algebraic_independent_equiv (e : ι ≃ ι') {f : ι' → A} :
  algebraic_independent R (f ∘ e) ↔ algebraic_independent R f :=
⟨λ h, function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
λ h, h.comp _ e.injective⟩

theorem algebraic_independent_equiv' (e : ι ≃ ι') {f : ι' → A} {g : ι → A} (h : f ∘ e = g) :
  algebraic_independent R g ↔ algebraic_independent R f :=
h ▸ algebraic_independent_equiv e

theorem algebraic_independent_subtype_range {ι} {f : ι → A} (hf : injective f) :
  algebraic_independent R (coe : range f → A) ↔ algebraic_independent R f :=
iff.symm $ algebraic_independent_equiv' (equiv.of_injective f hf) rfl

alias algebraic_independent_subtype_range ↔ algebraic_independent.of_subtype_range _

theorem algebraic_independent_image {ι} {s : set ι} {f : ι → A} (hf : set.inj_on f s) :
  algebraic_independent R (λ x : s, f x) ↔ algebraic_independent R (λ x : f '' s, (x : A)) :=
algebraic_independent_equiv' (equiv.set.image_of_inj_on _ _ hf) rfl

lemma algebraic_independent_adjoin (hs : algebraic_independent R x) :
  @algebraic_independent ι R (adjoin R (range x))
      (λ i : ι, ⟨x i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
algebraic_independent.of_comp (adjoin R (range x)).val hs

/-- A set of algebraically independent elements in an algebra `A` over a ring `K` is also
algebraically independent over a subring `R` of `K`. -/
lemma algebraic_independent.restrict_scalars {K : Type*} [comm_ring K] [algebra R K]
   [algebra K A] [is_scalar_tower R K A]
  (hinj : function.injective (algebra_map R K)) (ai : algebraic_independent K x) :
  algebraic_independent R x :=
have (aeval x : mv_polynomial ι K →ₐ[K] A).to_ring_hom.comp
    (mv_polynomial.map (algebra_map R K)) =
    (aeval x : mv_polynomial ι R →ₐ[R] A).to_ring_hom,
  by { ext; simp [algebra_map_eq_smul_one] },
begin
  show injective (aeval x).to_ring_hom,
  rw [← this],
  exact injective.comp ai (mv_polynomial.map_injective _ hinj)
end

/-- Every finite subset of an algebraically independent set is algebraically independent. -/
lemma algebraic_independent_finset_map_embedding_subtype
  (s : set A) (li : algebraic_independent R (coe : s → A)) (t : finset s) :
  algebraic_independent R (coe : (finset.map (embedding.subtype s) t) → A) :=
begin
  let f : t.map (embedding.subtype s) → s := λ x, ⟨x.1, begin
    obtain ⟨x, h⟩ := x,
    rw [finset.mem_map] at h,
    obtain ⟨a, ha, rfl⟩ := h,
    simp only [subtype.coe_prop, embedding.coe_subtype],
  end⟩,
  convert algebraic_independent.comp li f _,
  rintros ⟨x, hx⟩ ⟨y, hy⟩,
  rw [finset.mem_map] at hx hy,
  obtain ⟨a, ha, rfl⟩ := hx,
  obtain ⟨b, hb, rfl⟩ := hy,
  simp only [imp_self, subtype.mk_eq_mk],
end

/--
If every finite set of algebraically independent element has cardinality at most `n`,
then the same is true for arbitrary sets of algebraically independent elements.
-/
lemma algebraic_independent_bounded_of_finset_algebraic_independent_bounded {n : ℕ}
  (H : ∀ s : finset A, algebraic_independent R (λ i : s, (i : A)) → s.card ≤ n) :
  ∀ s : set A, algebraic_independent R (coe : s → A) → cardinal.mk s ≤ n :=
begin
  intros s li,
  apply cardinal.card_le_of,
  intro t,
  rw ← finset.card_map (embedding.subtype s),
  apply H,
  apply algebraic_independent_finset_map_embedding_subtype _ li,
end

section subtype

lemma algebraic_independent.restrict_of_comp_subtype {s : set ι}
  (hs : algebraic_independent R (x ∘ coe : s → A)) :
  algebraic_independent R (s.restrict x) :=
hs

variables (R A)
lemma algebraic_independent_empty_iff : algebraic_independent R (λ x, x : (∅ : set A) → A) ↔
  injective (algebra_map R A) :=
by simp
variables {R A}

lemma algebraic_independent.mono {t s : set A} (h : t ⊆ s)
  (hx : algebraic_independent R (λ x, x : s → A)) : algebraic_independent R (λ x, x : t → A) :=
by simpa [function.comp] using hx.comp (inclusion h) (inclusion_injective h)

end subtype

theorem algebraic_independent.to_subtype_range {ι} {f : ι → A} (hf : algebraic_independent R f) :
  algebraic_independent R (coe : range f → A) :=
begin
  nontriviality R,
  { rwa algebraic_independent_subtype_range hf.injective }
end

theorem algebraic_independent.to_subtype_range' {ι} {f : ι → A} (hf : algebraic_independent R f)
  {t} (ht : range f = t) :
  algebraic_independent R (coe : t → A) :=
ht ▸ hf.to_subtype_range

theorem algebraic_independent_comp_subtype {s : set ι} :
  algebraic_independent R (x ∘ coe : s → A) ↔
  ∀ p ∈ (mv_polynomial.supported R s), aeval x p = 0 → p = 0 :=
have (aeval (x ∘ coe : s → A) : _ →ₐ[R] _) =
  (aeval x).comp (rename coe), by ext; simp,
have ∀ p : mv_polynomial s R, rename (coe : s → ι) p = 0 ↔ p = 0,
  from (injective_iff_map_eq_zero' (rename (coe : s → ι) : mv_polynomial s R →ₐ[R] _).to_ring_hom).1
    (rename_injective _ subtype.val_injective),
by simp [algebraic_independent_iff, supported_eq_range_rename, *]

theorem algebraic_independent_subtype {s : set A} :
  algebraic_independent R (λ x, x : s → A) ↔
  ∀ (p : mv_polynomial A R), p ∈ mv_polynomial.supported R s → aeval id p = 0 → p = 0 :=
by apply @algebraic_independent_comp_subtype _ _ _ id

lemma algebraic_independent_of_finite (s : set A)
  (H : ∀ t ⊆ s, finite t → algebraic_independent R (λ x, x : t → A)) :
  algebraic_independent R (λ x, x : s → A) :=
algebraic_independent_subtype.2 $
  λ p hp, algebraic_independent_subtype.1 (H _ (mem_supported.1 hp) (finset.finite_to_set _)) _
    (by simp)

theorem algebraic_independent.image_of_comp {ι ι'} (s : set ι) (f : ι → ι') (g : ι' → A)
  (hs : algebraic_independent R (λ x : s, g (f x))) :
  algebraic_independent R (λ x : f '' s, g x) :=
begin
  nontriviality R,
  have : inj_on f s, from inj_on_iff_injective.2 hs.injective.of_comp,
  exact (algebraic_independent_equiv' (equiv.set.image_of_inj_on f s this) rfl).1 hs
end

theorem algebraic_independent.image {ι} {s : set ι} {f : ι → A}
  (hs : algebraic_independent R (λ x : s, f x)) : algebraic_independent R (λ x : f '' s, (x : A)) :=
by convert algebraic_independent.image_of_comp s f id hs

lemma algebraic_independent_Union_of_directed {η : Type*} [nonempty η]
  {s : η → set A} (hs : directed (⊆) s)
  (h : ∀ i, algebraic_independent R (λ x, x : s i → A)) :
  algebraic_independent R (λ x, x : (⋃ i, s i) → A) :=
begin
  refine algebraic_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
  rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
  rcases hs.finset_le fi.to_finset with ⟨i, hi⟩,
  exact (h i).mono (subset.trans hI $ Union₂_subset $
    λ j hj, hi j (fi.mem_to_finset.2 hj))
end

lemma algebraic_independent_sUnion_of_directed {s : set (set A)}
  (hsn : s.nonempty)
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, algebraic_independent R (λ x, x : (a : set A) → A)) :
  algebraic_independent R (λ x, x : (⋃₀ s) → A) :=
by letI : nonempty s := nonempty.to_subtype hsn;
rw sUnion_eq_Union; exact
algebraic_independent_Union_of_directed hs.directed_coe (by simpa using h)

lemma exists_maximal_algebraic_independent
  (s t : set A) (hst : s ⊆ t)
  (hs : algebraic_independent R (coe : s → A)) :
  ∃ u : set A, algebraic_independent R (coe : u → A) ∧ s ⊆ u ∧ u ⊆ t ∧
    ∀ x : set A, algebraic_independent R (coe : x → A) →
      u ⊆ x → x ⊆ t → x = u :=
begin
  rcases zorn_subset_nonempty
      { u : set A | algebraic_independent R (coe : u → A) ∧ s ⊆ u ∧ u ⊆ t }
    (λ c hc chainc hcn, ⟨⋃₀ c, begin
      refine ⟨⟨algebraic_independent_sUnion_of_directed hcn
        chainc.directed_on
        (λ a ha, (hc ha).1), _, _⟩, _⟩,
      { cases hcn with x hx,
        exact subset_sUnion_of_subset _ x (hc hx).2.1 hx },
      { exact sUnion_subset (λ x hx, (hc hx).2.2) },
      { intros s,
        exact subset_sUnion_of_mem }
    end⟩)
  s ⟨hs, set.subset.refl s, hst⟩ with ⟨u, ⟨huai, hsu, hut⟩, hsu, hx⟩,
  use [u, huai, hsu, hut],
  intros x hxai huv hxt,
  exact hx _ ⟨hxai, trans hsu huv, hxt⟩ huv,
end

section repr
variables (hx : algebraic_independent R x)

/-- Canonical isomorphism between polynomials and the subalgebra generated by
  algebraically independent elements. -/
@[simps] def algebraic_independent.aeval_equiv (hx : algebraic_independent R x) :
  (mv_polynomial ι R) ≃ₐ[R] algebra.adjoin R (range x) :=
begin
  apply alg_equiv.of_bijective
    (alg_hom.cod_restrict (@aeval R A ι _ _ _ x) (algebra.adjoin R (range x)) _),
  swap,
  { intros x,
    rw [adjoin_range_eq_range_aeval],
    exact alg_hom.mem_range_self _ _ },
  { split,
    { exact (alg_hom.injective_cod_restrict _ _ _).2 hx },
    { rintros ⟨x, hx⟩,
      rw [adjoin_range_eq_range_aeval] at hx,
      rcases hx with ⟨y, rfl⟩,
      use y,
      ext,
      simp } }
end

@[simp] lemma algebraic_independent.algebra_map_aeval_equiv (hx : algebraic_independent R x)
  (p : mv_polynomial ι R) : algebra_map (algebra.adjoin R (range x)) A (hx.aeval_equiv p) =
  aeval x p := rfl

/-- The canonical map from the subalgebra generated by an algebraic independent family
  into the polynomial ring.  -/
def algebraic_independent.repr (hx : algebraic_independent R x) :
  algebra.adjoin R (range x) →ₐ[R] mv_polynomial ι R := hx.aeval_equiv.symm

@[simp] lemma algebraic_independent.aeval_repr (p) : aeval x (hx.repr p) = p :=
subtype.ext_iff.1 (alg_equiv.apply_symm_apply hx.aeval_equiv p)

lemma algebraic_independent.aeval_comp_repr :
  (aeval x).comp hx.repr = subalgebra.val _ :=
alg_hom.ext $ hx.aeval_repr

lemma algebraic_independent.repr_ker :
  (hx.repr : adjoin R (range x) →+* mv_polynomial ι R).ker = ⊥ :=
(ring_hom.injective_iff_ker_eq_bot _).1 (alg_equiv.injective _)

end repr

-- TODO - make this an `alg_equiv`
/-- The isomorphism between `mv_polynomial (option ι) R` and the polynomial ring over
the algebra generated by an algebraically independent family.  -/
def algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin
  (hx : algebraic_independent R x) :
  mv_polynomial (option ι) R ≃+* polynomial (adjoin R (set.range x)) :=
(mv_polynomial.option_equiv_left _ _).to_ring_equiv.trans
  (polynomial.map_equiv hx.aeval_equiv.to_ring_equiv)

@[simp]
lemma algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply
  (hx : algebraic_independent R x) (y) :
  hx.mv_polynomial_option_equiv_polynomial_adjoin y =
    polynomial.map (hx.aeval_equiv : mv_polynomial ι R →+* adjoin R (range x))
      (aeval (λ (o : option ι), o.elim polynomial.X (λ (s : ι), polynomial.C (X s))) y) :=
rfl

@[simp]
lemma algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_C
  (hx : algebraic_independent R x) (r) :
  hx.mv_polynomial_option_equiv_polynomial_adjoin (C r) =
    polynomial.C (algebra_map _ _ r) :=
begin
  -- TODO: this instance is slow to infer
  have h : is_scalar_tower R (mv_polynomial ι R) (polynomial (mv_polynomial ι R)) :=
    @polynomial.is_scalar_tower (mv_polynomial ι R) _ R _ _ _ _ _ _ _,
  rw [algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply, aeval_C,
    @is_scalar_tower.algebra_map_apply _ _ _ _ _ _ _ _ _ h, ← polynomial.C_eq_algebra_map,
    polynomial.map_C, ring_hom.coe_coe, alg_equiv.commutes]
end

@[simp]
lemma algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_none
  (hx : algebraic_independent R x) :
  hx.mv_polynomial_option_equiv_polynomial_adjoin (X none) = polynomial.X :=
by rw [algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply, aeval_X,
      option.elim, polynomial.map_X]

@[simp]
lemma algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_some
  (hx : algebraic_independent R x) (i) :
  hx.mv_polynomial_option_equiv_polynomial_adjoin (X (some i)) =
    polynomial.C (hx.aeval_equiv (X i)) :=
by rw [algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply, aeval_X,
      option.elim, polynomial.map_C, ring_hom.coe_coe]

lemma algebraic_independent.aeval_comp_mv_polynomial_option_equiv_polynomial_adjoin
  (hx : algebraic_independent R x) (a : A) :
  (ring_hom.comp (↑(polynomial.aeval a : polynomial (adjoin R (set.range x)) →ₐ[_] A) :
      polynomial (adjoin R (set.range x)) →+* A)
    hx.mv_polynomial_option_equiv_polynomial_adjoin.to_ring_hom) =
    ↑((mv_polynomial.aeval (λ o : option ι, o.elim a x)) :
      mv_polynomial (option ι) R →ₐ[R] A) :=
begin
  refine mv_polynomial.ring_hom_ext _ _;
    simp only [ring_hom.comp_apply, ring_equiv.to_ring_hom_eq_coe, ring_equiv.coe_to_ring_hom,
        alg_hom.coe_to_ring_hom, alg_hom.coe_to_ring_hom],
  { intro r,
    rw [hx.mv_polynomial_option_equiv_polynomial_adjoin_C,
        aeval_C, polynomial.aeval_C, is_scalar_tower.algebra_map_apply R (adjoin R (range x)) A] },
  { rintro (⟨⟩|⟨i⟩),
    { rw [hx.mv_polynomial_option_equiv_polynomial_adjoin_X_none,
          aeval_X, polynomial.aeval_X, option.elim] },
    { rw [hx.mv_polynomial_option_equiv_polynomial_adjoin_X_some, polynomial.aeval_C,
          hx.algebra_map_aeval_equiv, aeval_X, aeval_X, option.elim] } },
end

theorem algebraic_independent.option_iff (hx : algebraic_independent R x) (a : A) :
  (algebraic_independent R (λ o : option ι, o.elim a x)) ↔
    ¬ is_algebraic (adjoin R (set.range x)) a :=
by erw [algebraic_independent_iff_injective_aeval, is_algebraic_iff_not_injective, not_not,
    ← alg_hom.coe_to_ring_hom,
    ← hx.aeval_comp_mv_polynomial_option_equiv_polynomial_adjoin,
    ring_hom.coe_comp, injective.of_comp_iff' _ (ring_equiv.bijective _), alg_hom.coe_to_ring_hom]

variable (R)
/--
  A family is a transcendence basis if it is a maximal algebraically independent subset.
-/
def is_transcendence_basis (x : ι → A) : Prop :=
algebraic_independent R x ∧
  ∀ (s : set A) (i' : algebraic_independent R (coe : s → A)) (h : range x ≤ s), range x = s

lemma exists_is_transcendence_basis (h : injective (algebra_map R A)) :
  ∃ s : set A, is_transcendence_basis R (coe : s → A) :=
begin
  cases exists_maximal_algebraic_independent (∅ : set A) set.univ
    (set.subset_univ _) ((algebraic_independent_empty_iff R A).2 h) with s hs,
  use [s, hs.1],
  intros t ht hr,
  simp only [subtype.range_coe_subtype, set_of_mem_eq] at *,
  exact eq.symm (hs.2.2.2 t ht hr (set.subset_univ _))
end

variable {R}
lemma algebraic_independent.is_transcendence_basis_iff
  {ι : Type w} {R : Type u} [comm_ring R] [nontrivial R]
  {A : Type v} [comm_ring A] [algebra R A] {x : ι → A} (i : algebraic_independent R x) :
  is_transcendence_basis R x ↔ ∀ (κ : Type v) (w : κ → A) (i' : algebraic_independent R w)
    (j : ι → κ) (h : w ∘ j = x), surjective j :=
begin
  fsplit,
  { rintros p κ w i' j rfl,
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _),
    rw [range_comp, ←@image_univ _ _ w] at p,
    exact range_iff_surjective.mp (image_injective.mpr i'.injective p) },
  { intros p,
    use i,
    intros w i' h,
    specialize p w (coe : w → A) i'
      (λ i, ⟨x i, range_subset_iff.mp h i⟩)
      (by { ext, simp, }),
    have q := congr_arg (λ s, (coe : w → A) '' s) p.range_eq,
    dsimp at q,
    rw [←image_univ, image_image] at q,
    simpa using q, },
end

lemma is_transcendence_basis.is_algebraic [nontrivial R]
  (hx : is_transcendence_basis R x) : is_algebraic (adjoin R (range x)) A :=
begin
  intro a,
  rw [← not_iff_comm.1 (hx.1.option_iff _).symm],
  intro ai,
  have h₁ : range x ⊆ range (λ o : option ι, o.elim a x),
  { rintros x ⟨y, rfl⟩, exact ⟨some y, rfl⟩ },
  have h₂ : range x ≠ range (λ o : option ι, o.elim a x),
  { intro h,
    have : a ∈ range x, { rw h, exact ⟨none, rfl⟩ },
    rcases this with ⟨b, rfl⟩,
    have : some b = none := ai.injective rfl,
    simpa },
  exact h₂ (hx.2 (set.range (λ o : option ι, o.elim a x))
    ((algebraic_independent_subtype_range ai.injective).2 ai) h₁)
end

section field
variables [field K] [algebra K A]

@[simp] lemma algebraic_independent_empty_type [is_empty ι] [nontrivial A] :
  algebraic_independent K x :=
begin
  rw [algebraic_independent_empty_type_iff],
  exact ring_hom.injective _,
end

lemma algebraic_independent_empty [nontrivial A] :
  algebraic_independent K (coe : ((∅ : set A) → A)) :=
algebraic_independent_empty_type

end field
