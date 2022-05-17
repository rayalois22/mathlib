/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.continuous_on
import data.setoid.basic
import tactic.tfae

/-!
# Inseparable points in a topological space

In this file we define

* `inseparable x y`: a predicate saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `~` is used as a local notation for `inseparable`;
- `𝓝 x` is the neighbourhoods filter of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/

open set filter function
open_locale topological_space

variables {X Y : Type*} [topological_space X] [topological_space Y] {x y z : X}
  {s : set X} {f : X → Y}

lemma nhds_le_nhds_tfae (x y : X) :
  tfae [𝓝 x ≤ 𝓝 y,
    pure x ≤ 𝓝 y,
    ∀ s : set X, is_open s → y ∈ s → x ∈ s,
    ∀ s : set X, is_closed s → x ∈ s → y ∈ s,
    y ∈ closure ({x} : set X),
    cluster_pt y (pure x)] :=
begin
  tfae_have : 1 → 2, from (pure_le_nhds _).trans,
  tfae_have : 2 → 3, from λ h s hso hy, h (hso.mem_nhds hy),
  tfae_have : 3 → 4, from λ h s hsc hx, of_not_not $ λ hy, h sᶜ hsc.is_open_compl hy hx,
  tfae_have : 4 → 5, from λ h, h _ is_closed_closure (subset_closure $ mem_singleton _),
  tfae_have : 5 ↔ 6, by rw [mem_closure_iff_cluster_pt, principal_singleton],
  tfae_have : 6 → 1,
  { refine λ h, (nhds_basis_opens _).ge_iff.2 _,
    rintro s ⟨hy, ho⟩,
    have := cluster_pt_iff.1 h (ho.mem_nhds hy) (mem_pure.2 $ mem_singleton _),
    exact ho.mem_nhds (inter_singleton_nonempty.1 this) },
  tfae_finish
end

lemma nhds_le_nhds_iff_pure : 𝓝 x ≤ 𝓝 y ↔ pure x ≤ 𝓝 y :=
(nhds_le_nhds_tfae x y).out 0 1

lemma nhds_le_nhds_iff_open : 𝓝 x ≤ 𝓝 y ↔ ∀ ⦃s : set X⦄, is_open s → y ∈ s → x ∈ s :=
(nhds_le_nhds_tfae x y).out 0 2

lemma nhds_le_nhds_iff_closed : 𝓝 x ≤ 𝓝 y ↔ ∀ ⦃s : set X⦄, is_closed s → x ∈ s → y ∈ s :=
(nhds_le_nhds_tfae x y).out 0 3

lemma nhds_le_nhds_iff_mem_closure : 𝓝 x ≤ 𝓝 y ↔ y ∈ closure ({x} : set X) :=
(nhds_le_nhds_tfae x y).out 0 4

lemma nhds_le_nhds_iff_cluster_pt : 𝓝 x ≤ 𝓝 y ↔ cluster_pt y (pure x) :=
(nhds_le_nhds_tfae x y).out 0 5

lemma nhds_le_nhds_of_nhds_within (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : 𝓝 x ≤ 𝓝 y :=
nhds_le_nhds_iff_pure.2 $
calc pure x ≤ 𝓝[s] x : le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
        ... ≤ 𝓝[s] y : h₁
        ... ≤ 𝓝 y    : inf_le_left

lemma nhds_le_nhds_of_continuous_at (h : 𝓝 x ≤ 𝓝 y) (hy : continuous_at f y) :
  𝓝 (f x) ≤ 𝓝 (f y) :=
nhds_le_nhds_iff_pure.2 $ λ s hs, mem_pure.2 $ mem_preimage.1 $ mem_of_mem_nhds $ hy.mono_left h hs

/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`.
-/
def inseparable (x y : X) : Prop := 𝓝 x = 𝓝 y

local infix ` ~ ` := inseparable

lemma inseparable_def : x ~ y ↔ 𝓝 x = 𝓝 y := iff.rfl

lemma inseparable_iff_open : x ~ y ↔ ∀ s : set X, is_open s → (x ∈ s ↔ y ∈ s) :=
by simp only [inseparable, le_antisymm_iff, nhds_le_nhds_iff_open, ← forall_and_distrib, ← iff_def,
  iff.comm]

lemma not_inseparable_iff_open : ¬(x ~ y) ↔ ∃ s : set X, is_open s ∧ xor (x ∈ s) (y ∈ s) :=
by simp [inseparable_iff_open, ← xor_iff_not_iff]

lemma inseparable_iff_closed : x ~ y ↔ ∀ s : set X, is_closed s → (x ∈ s ↔ y ∈ s) :=
by simp only [inseparable, le_antisymm_iff, nhds_le_nhds_iff_closed, ← forall_and_distrib,
  ← iff_def]

lemma inseparable_iff_mem_closure :
  x ~ y ↔ x ∈ closure ({y} : set X) ∧ y ∈ closure ({x} : set X) :=
le_antisymm_iff.trans $ by simp only [nhds_le_nhds_iff_mem_closure, and_comm]

lemma inseparable_of_nhds_within_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ y :=
le_antisymm (nhds_le_nhds_of_nhds_within h.le hx) (nhds_le_nhds_of_nhds_within h.ge hy)

lemma inducing.inseparable_iff (hf : inducing f) : f x ~ f y ↔ x ~ y :=
by simp only [inseparable_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
  mem_preimage]

namespace inseparable

@[refl] lemma refl (x : X) : x ~ x := eq.refl (𝓝 x)

lemma rfl : x ~ x := refl x

@[symm] lemma symm (h : x ~ y) : y ~ x := h.symm

@[trans] lemma trans (h₁ : x ~ y) (h₂ : y ~ z) : x ~ z := h₁.trans h₂

lemma nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y := h

lemma mem_open_iff (h : x ~ y) (hs : is_open s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_open.1 h s hs

lemma mem_closed_iff (h : x ~ y) (hs : is_closed s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_closed.1 h s hs

lemma map_of_continuous_at (h : x ~ y) (hx : continuous_at f x) (hy : continuous_at f y) :
  f x ~ f y :=
le_antisymm (nhds_le_nhds_of_continuous_at h.le hy) (nhds_le_nhds_of_continuous_at h.ge hx)

lemma map (h : x ~ y) (hf : continuous f) : f x ~ f y :=
h.map_of_continuous_at hf.continuous_at hf.continuous_at

end inseparable

lemma is_closed.not_inseparable (hs : is_closed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ~ y :=
λ h, hy $ (h.mem_closed_iff hs).1 hx

lemma is_open.not_inseparable (hs : is_open s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ~ y :=
λ h, hy $ (h.mem_open_iff hs).1 hx

variable (X)

/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparable_setoid : setoid X :=
{ r := (~),
  .. setoid.comap 𝓝 ⊥ }

/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a T₀ space. -/
@[derive topological_space]
def separation_quotient := quotient (inseparable_setoid X)

variable {X}

namespace separation_quotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → separation_quotient X := quotient.mk'

lemma quotient_map_mk : quotient_map (mk : X → separation_quotient X) :=
quotient_map_quot_mk

lemma continuous_mk : continuous (mk : X → separation_quotient X) :=
continuous_quot_mk

@[simp] lemma mk_eq_mk : mk x = mk y ↔ x ~ y := quotient.eq'

lemma surjective_mk : surjective (mk : X → separation_quotient X) :=
surjective_quot_mk _

@[simp] lemma range_mk : range (mk : X → separation_quotient X) = univ :=
surjective_mk.range_eq

lemma preimage_image_mk_open (hs : is_open s) : mk ⁻¹' (mk '' s) = s :=
begin
  refine subset.antisymm _ (subset_preimage_image _ _),
  rintro x ⟨y, hys, hxy⟩,
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys
end

lemma is_open_map_mk : is_open_map (mk : X → separation_quotient X) :=
λ s hs, quotient_map_mk.is_open_preimage.1 $ by rwa preimage_image_mk_open hs

lemma preimage_image_mk_closed (hs : is_closed s) : mk ⁻¹' (mk '' s) = s :=
begin
  refine subset.antisymm _ (subset_preimage_image _ _),
  rintro x ⟨y, hys, hxy⟩,
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys
end

lemma inducing_mk : inducing (mk : X → separation_quotient X) :=
⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk)
  (λ s hs, ⟨mk '' s, is_open_map_mk s hs, preimage_image_mk_open hs⟩)⟩

lemma is_closed_map_mk : is_closed_map (mk : X → separation_quotient X) :=
inducing_mk.is_closed_map $ by { rw [range_mk], exact is_closed_univ }

lemma map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) :=
by rw [inducing_mk.nhds_eq_comap, map_comap_of_surjective surjective_mk]

end separation_quotient
