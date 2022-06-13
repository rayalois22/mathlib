/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import field_theory.normal
import field_theory.is_alg_closed.algebraic_closure

/-!
# Normal closures

Let L/K be a finite field extension. The normal closure N/L of L/K is a finite extension
N/L such that N/K is normal and which is informally "the smallest extension with this property".
More formally we could say that if M/L is algebraic and M/K is normal then there exists
a morphism of K-algebras `N →ₐ[K] M`. Note that this morphism may not be unique, and
indeed `N` is only defined up to a non-unique isomorphism in general.

## Main Definitions

- `normal_closure K L` where `L` is a field extension of the field `K`, of finite degree.
-/

section field_range

def alg_hom.field_range {F K L : Type*} [field F] [field K] [field L] [algebra F K]
  [algebra F L] (φ : K →ₐ[F] L) : intermediate_field F L :=
{ ..φ.range,
  ..φ.to_ring_hom.field_range }

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def alg_hom.field_range_restrict {F K L : Type*} [field F] [field K] [field L] [algebra F K]
  [algebra F L] (φ : K →ₐ[F] L) : K →ₐ[F] φ.field_range :=
φ.cod_restrict φ.range φ.mem_range_self

end field_range

section inclusion

noncomputable lemma intermediate_field.inclusion {K L : Type*} [field K] [field L] [algebra K L]
  {S T : intermediate_field K L} (h : S ≤ T) : (↥S →ₐ[K] ↥T) :=
subalgebra.inclusion h

end inclusion

section normal_iff_invariant

variables (K L : Type*) [field K] [field L] [algebra K L]

lemma normal_iff_galois_stable (h : algebra.is_algebraic K L) : normal K L ↔
  ∀ φ : L →ₐ[K] algebraic_closure L, φ.field_range ≤
    (is_scalar_tower.to_alg_hom K L (algebraic_closure L)).field_range :=
begin
  sorry
end


end normal_iff_invariant

variables (K L : Type*) [field K] [field L] [algebra K L]

private noncomputable def normal_closure_aux : intermediate_field K (algebraic_closure L) :=
supr (λ φ : (L →ₐ[K] algebraic_closure L), φ.field_range)

namespace normal_closure

lemma le_closure_aux : (is_scalar_tower.to_alg_hom K L (algebraic_closure L)).field_range ≤
  normal_closure_aux K L :=
le_supr _ _

noncomputable! def normal_closure (K L : Type*) [field K] [field L] [algebra K L] :
intermediate_field L (algebraic_closure L) :=
{ carrier := normal_closure_aux K L,
  algebra_map_mem' := λ r, le_closure_aux _ _ ⟨r, rfl⟩,
  ..normal_closure_aux K L }

-- instance : is_scalar_tower K L (normal_closure K L) := infer_instance

instance : is_scalar_tower L (normal_closure K L) (algebraic_closure L) :=
(normal_closure K L).is_scalar_tower_mid' -- infer_instance doesn't work here for some reason

lemma is_algebraic (h : algebra.is_algebraic K L) : algebra.is_algebraic K (normal_closure K L) :=
begin
  refine algebra.is_algebraic_trans h _,
  rintro x,
  obtain ⟨p, hp1, hp2⟩ := algebraic_closure.is_algebraic L (x : algebraic_closure L),
  refine ⟨p, hp1, subtype.ext _⟩,
  exact_mod_cast hp2,
end

-- useful to know?
-- example (h : algebra.is_algebraic K L) : is_alg_closure K (algebraic_closure L) :=
-- begin
--   rw is_alg_closure_iff,
--   exact ⟨algebraic_closure.is_alg_closed L, algebra.is_algebraic_trans h is_alg_closure.algebraic⟩,
-- end

lemma is_normal (h : algebra.is_algebraic K L) : normal K (normal_closure K L) :=
begin
  rw normal_iff_galois_stable _ _ (is_algebraic K L h),
  intro φ,
  sorry,
end

lemma is_finite_dimensional [finite_dimensional K L] : finite_dimensional K (normal_closure K L) :=
sorry

end normal_closure
