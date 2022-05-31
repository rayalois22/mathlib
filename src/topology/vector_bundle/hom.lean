/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import topology.vector_bundle
import analysis.normed_space.operator_norm

/-! # The bundle of continuous linear maps between two vector bundles over the same base -/

noncomputable theory

open bundle set continuous_linear_map

section move

lemma continuous_clm_comp
{𝕜₁} [nondiscrete_normed_field 𝕜₁]
{F₁} [normed_group F₁] [normed_space 𝕜₁ F₁]
{F₂} [normed_group F₂] [normed_space 𝕜₁ F₂]
{F₃} [normed_group F₃] [normed_space 𝕜₁ F₃] :
  continuous (λ x : (F₂ →L[𝕜₁] F₃) × (F₁ →L[𝕜₁] F₂), x.1.comp x.2) :=
(compL 𝕜₁ F₁ F₂ F₃).continuous₂

lemma continuous.clm_comp {X} [topological_space X]
{𝕜₁} [nondiscrete_normed_field 𝕜₁]
{F₁} [normed_group F₁] [normed_space 𝕜₁ F₁]
{F₂} [normed_group F₂] [normed_space 𝕜₁ F₂]
{F₃} [normed_group F₃] [normed_space 𝕜₁ F₃] {f : X → F₁ →L[𝕜₁] F₂}
  {g : X → F₂ →L[𝕜₁] F₃} (hf : continuous f)
  (hg : continuous g) :
  continuous (λ x, (g x).comp (f x)) :=
(compL 𝕜₁ F₁ F₂ F₃).continuous₂.comp₂ hg hf

lemma continuous_on.clm_comp {X} [topological_space X]
{𝕜₁} [nondiscrete_normed_field 𝕜₁]
{F₁} [normed_group F₁] [normed_space 𝕜₁ F₁]
{F₂} [normed_group F₂] [normed_space 𝕜₁ F₂]
{F₃} [normed_group F₃] [normed_space 𝕜₁ F₃] {f : X → F₁ →L[𝕜₁] F₂}
  {g : X → F₂ →L[𝕜₁] F₃} {s : set X} (hf : continuous_on f s)
  (hg : continuous_on g s) :
  continuous_on (λ x, (g x).comp (f x)) s :=
(compL 𝕜₁ F₁ F₂ F₃).continuous₂.comp_continuous_on (hg.prod hf)

end move

namespace topological_vector_bundle


section defs
variables {𝕜₁ : Type*} [normed_field 𝕜₁]
variables {𝕜₂ : Type*} [normed_field 𝕜₂]
variables (σ : 𝕜₁ →+* 𝕜₂)
variables {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [Π x, has_continuous_add (E₁ x)]
  [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [Π x, has_continuous_add (E₂ x)]
  [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

include F₁ F₂

-- In this definition we require the scalar rings `𝕜₁` and `𝕜₂` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`.  Type synonym for `λ x, E₁ x →SL[σ] E₂ x`. -/
@[derive [add_comm_monoid, module 𝕜₂, inhabited], nolint unused_arguments]
def vector_bundle_continuous_linear_map (x : B) : Type* :=
E₁ x →SL[σ] E₂ x

instance vector_bundle_continuous_linear_map.add_monoid_hom_class (x : B) :
  add_monoid_hom_class (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) (E₁ x) (E₂ x) :=
continuous_linear_map.add_monoid_hom_class

end defs

variables {𝕜₁ : Type*} [nondiscrete_normed_field 𝕜₁] {𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂)

variables {B : Type*} [topological_space B]

variables (F₁ : Type*) [normed_group F₁] [normed_space 𝕜₁ F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]
  [Π x, has_continuous_add (E₁ x)] [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  [topological_vector_bundle 𝕜₁ F₁ E₁]

variables (F₂ : Type*) [normed_group F₂][normed_space 𝕜₂ F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]
  [topological_vector_bundle 𝕜₂ F₂ E₂]

namespace pretrivialization

variables (e₁ e₁' : trivialization 𝕜₁ F₁ E₁) (e₂ e₂' : trivialization 𝕜₂ F₂ E₂)

include e₁ e₂
variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` to `E₂`. -/
def continuous_linear_map.to_fun'
  (p : total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  B × (F₁ →SL[σ] F₂) :=
⟨p.1, (e₂.continuous_linear_map_at p.1).comp $ p.2.comp $ e₁.symmL p.1⟩

variables {σ e₁ e₂}

lemma continuous_linear_map.to_fun'_apply' (x : B) (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map.to_fun' σ e₁ e₂
    (@coe _ _ (@coe_to_lift _ _
      (@total_space.has_coe_t B (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) x)) L)
  = ⟨x, (e₂.continuous_linear_map_at x).comp $ L.comp $ e₁.symmL x⟩ :=
rfl

variables (σ e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` and `E₂`. -/
def continuous_linear_map.inv_fun' (p : B × (F₁ →SL[σ] F₂)) :
  total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
⟨p.1, (e₂.symmL p.1).comp $ p.2.comp $ e₁.continuous_linear_map_at p.1⟩

variables [ring_hom_isometric σ]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`.  That is, the map which
will later become a trivialization, after this direct sum is equipped with the right topological
vector bundle structure. -/
def continuous_linear_map :
  pretrivialization 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ to_fun := continuous_linear_map.to_fun' σ e₁ e₂,
  inv_fun := continuous_linear_map.inv_fun' σ e₁ e₂,
  source := (proj (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) ⁻¹'
    (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ →SL[σ] F₂)),
  map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
  begin
    simp_rw [continuous_linear_map.to_fun', continuous_linear_map.inv_fun',
      sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
    ext v,
    simp only [comp_apply, trivialization.symmL_continuous_linear_map_at,
      h₁, h₂]
  end,
  right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
  begin
    simp_rw [continuous_linear_map.inv_fun', continuous_linear_map.to_fun',
      prod.mk.inj_iff, eq_self_iff_true, true_and],
    ext v,
    simp only [comp_apply, trivialization.continuous_linear_map_at_symmL,
      h₁, h₂]
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl,
  linear' := λ x h,
  { map_add := λ L L', by simp_rw [continuous_linear_map.to_fun'_apply', add_comp, comp_add],
    map_smul := λ c L, by simp_rw [continuous_linear_map.to_fun'_apply', smul_comp, comp_smulₛₗ,
      ring_hom.id_apply]} }

lemma continuous_linear_map_apply :
  ⇑(continuous_linear_map σ e₁ e₂) = continuous_linear_map.to_fun' σ e₁ e₂ :=
rfl

lemma continuous_linear_map_symm_apply :
  ⇑(continuous_linear_map σ e₁ e₂).to_local_equiv.symm = continuous_linear_map.inv_fun' σ e₁ e₂ :=
rfl

lemma continuous_linear_map_symm_apply' {b : B} (hb : b ∈ e₁.base_set ∩ e₂.base_set)
  (L : F₁ →SL[σ] F₂) :
  (continuous_linear_map σ e₁ e₂).symm b L =
  (e₂.symmL b).comp (L.comp $ e₁.continuous_linear_map_at b) :=
begin
  rw [symm_apply], refl, exact hb
end

def continuous_linear_map_coord_change (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
((e₁'.coord_change e₁ b).symm.arrow_congrSL (e₂.coord_change e₂' b) :
  (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)

-- move
attribute [simps apply {simp_rhs := tt}] continuous_linear_equiv.arrow_congrSL

lemma continuous_linear_map_coord_change_apply (b : B)
  (hb : b ∈ (e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) (L : F₁ →SL[σ] F₂) :
  continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂' b L =
  (continuous_linear_map σ e₁' e₂'
    (total_space_mk _ b ((continuous_linear_map σ e₁ e₂).symm b L))).2 :=
begin
  ext v,
  simp_rw [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
    continuous_linear_equiv.arrow_congrSL_apply,
    continuous_linear_map_apply, continuous_linear_map.to_fun',
    continuous_linear_map_symm_apply' σ e₁ e₂ hb.1,
    comp_apply, continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_symm,
    trivialization.continuous_linear_map_at_apply, trivialization.symmL_apply],
  dsimp only [total_space_mk],
  rw [e₂.coord_change_apply e₂', e₁'.coord_change_apply e₁, e₁.coe_linear_map_at_of_mem hb.1.1,
    e₂'.coe_linear_map_at_of_mem hb.2.2],
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
end

variables {σ e₁ e₁' e₂ e₂'}

lemma continuous_on_continuous_linear_map_coord_change
  (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁) (he₁' : e₁' ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) (he₂' : e₂' ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  continuous_on (continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂')
    ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
  have h₁ := (compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂)).continuous,
  have h₂ := (continuous_linear_map.flip (compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ)).continuous,
  have h₃ := (continuous_on_coord_change e₁' he₁' e₁ he₁),
  have h₄ := (continuous_on_coord_change e₂ he₂ e₂' he₂'),
  refine ((h₂.comp_continuous_on (h₃.mono _)).clm_comp (h₁.comp_continuous_on (h₄.mono _))).congr _,
  { mfld_set_tac },
  { mfld_set_tac },
  { intros b hb, ext L v,
    simp only [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.arrow_congrSL_apply, comp_apply, function.comp, compSL_apply,
      flip_apply, continuous_linear_equiv.symm_symm] },
end

end pretrivialization

open pretrivialization
variables [ring_hom_isometric σ]

-- this instance is needed if we don't change the definition of `topological_vector_prebundle`.
-- instance (b : B) : topological_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ b) :=
-- topological_space.induced (λ x : vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ b,
--   pretrivialization.continuous_linear_map σ
--     (trivialization_at 𝕜₁ F₁ E₁ b) (trivialization_at 𝕜₂ F₂ E₂ b)
--     (total_space_mk (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) b x))
--     _root_.prod.topological_space

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`topological_vector_prebundle` (this is an auxiliary construction for the
`topological_vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.vector_bundle_continuous_linear_map.topological_vector_prebundle :
  topological_vector_prebundle 𝕜₂ (F₁ →SL[σ] F₂)
  (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ pretrivialization_atlas :=
  image2 (λ e₁ e₂, pretrivialization.continuous_linear_map σ e₁ e₂) (trivialization_atlas 𝕜₁ F₁ E₁)
    (trivialization_atlas 𝕜₂ F₂ E₂),
-- ⋃ (e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
--     (e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂), {pretrivialization.continuous_linear_map σ e₁ e₂},
  pretrivialization_at := λ x, pretrivialization.continuous_linear_map σ
    (trivialization_at 𝕜₁ F₁ E₁ x) (trivialization_at 𝕜₂ F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x, mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x⟩,
  pretrivialization_mem_atlas := λ x,
    ⟨_, _, trivialization_mem_atlas 𝕜₁ F₁ E₁ x, trivialization_mem_atlas 𝕜₂ F₂ E₂ x, rfl⟩,
  exists_coord_change := by { rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    exact ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
    continuous_on_continuous_linear_map_coord_change he₁ he₁' he₂ he₂',
    continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩ } }

-- /-- Topology on the continuous `σ`-semilinear_maps between the respective fibres at a point of two
-- "normable" vector bundles over the same base. Here "normable" means that the bundles have fibres
-- modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous
-- `σ`-semilinear_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
-- instance (x : B) : topological_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) :=
-- (vector_bundle_continuous_linear_map.topological_vector_prebundle σ F₁ E₁ F₂ E₂).fiber_topology x

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance : topological_space (total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance vector_bundle_continuous_linear_map.topological_vector_bundle :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).to_topological_vector_bundle

variables {F₁ E₁ F₂ E₂}

-- /-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
-- trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`, whose base set is
-- `e₁.base_set ∩ e₂.base_set`.
-- -/
-- def trivialization.continuous_linear_map
--   (e₁ : trivialization 𝕜₁ F₁ E₁) (e₂ : trivialization 𝕜₂ F₂ E₂) :
--   trivialization 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
-- { open_source := (continuous_linear_map σ e₁ e₂).open_base_set.preimage
--     (topological_vector_bundle.continuous_proj 𝕜₂ B (F₁ →SL[σ] F₂)),
--   continuous_to_fun :=
--   begin
--     apply topological_fiber_prebundle.continuous_on_of_comp_right,
--     { exact e₁.open_base_set.inter e₂.open_base_set },
--     intros b,
--     convert continuous_triv_change_continuous_linear_map e₁ (trivialization_at 𝕜₁ F₁ E₁ b) e₂
--       (trivialization_at 𝕜₂ F₂ E₂ b),
--     rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--     refl,
--   end,
--   continuous_inv_fun := λ x hx, continuous_at.continuous_within_at
--   begin
--     let f₁ := trivialization_at 𝕜₁ F₁ E₁ x.1,
--     let f₂ := trivialization_at 𝕜₂ F₂ E₂ x.1,
--     have H : (continuous_linear_map σ e₁ e₂).target
--       ∩ (continuous_linear_map σ e₁ e₂).to_local_equiv.symm ⁻¹'
--       (continuous_linear_map σ f₁ f₂).source ∈ nhds x,
--     { rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--       refine is_open.mem_nhds _ ⟨⟨_, hx.1⟩, mem_univ _⟩,
--       { exact ((continuous_linear_map σ f₁ f₂).open_base_set.inter
--           (continuous_linear_map σ e₁ e₂).open_base_set).prod is_open_univ },
--       { exact ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x.1,
--           mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x.1⟩ } },
--     let a := (vector_bundle_continuous_linear_map.topological_vector_prebundle
--       σ F₁ E₁ F₂ E₂).to_topological_fiber_prebundle,
--     rw (a.trivialization_at x.1).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
--     { exact (continuous_triv_change_continuous_linear_map f₁ e₁ f₂ e₂).continuous_at H },
--     { exact filter.mem_of_superset H (inter_subset_right _ _) },
--   end,
--   .. pretrivialization.continuous_linear_map σ e₁ e₂ }

-- @[simp] lemma trivialization.base_set_continuous_linear_map (e₁ : trivialization 𝕜₁ F₁ E₁)
--   (e₂ : trivialization 𝕜₂ F₂ E₂) :
--   (e₁.continuous_linear_map σ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
-- rfl

-- lemma trivialization.continuous_linear_map_apply
--   {e₁ : trivialization 𝕜₁ F₁ E₁} {e₂ : trivialization 𝕜₂ F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set)
--   (hx₂ : x ∈ e₂.base_set) (L : E₁ x →SL[σ] E₂ x) :
--   e₁.continuous_linear_map σ e₂ ⟨x, L⟩
--   = ⟨x, (e₂.continuous_linear_equiv_at x hx₂ : E₂ x →L[𝕜₂] F₂).comp (L.comp
--       ((e₁.continuous_linear_equiv_at x hx₁).symm : F₁ →L[𝕜₁] E₁ x))⟩ :=
-- pretrivialization.continuous_linear_map_apply hx₁ hx₂ L

-- lemma trivialization.continuous_linear_equiv_at_continuous_linear_map
--   {e₁ : trivialization 𝕜₁ F₁ E₁} {e₂ : trivialization 𝕜₂ F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set)
--   (hx₂ : x ∈ e₂.base_set)  :
--   ((e₁.continuous_linear_map σ e₂).continuous_linear_equiv_at x ⟨hx₁, hx₂⟩).to_linear_equiv
--   = continuous_linear_equiv.arrow_congr_linear_equiv σ
--       (e₁.continuous_linear_equiv_at x hx₁)
--       (e₂.continuous_linear_equiv_at x hx₂) :=
-- begin
--   ext1,
--   simp [trivialization.continuous_linear_map_apply σ hx₁ hx₂],
-- end

end topological_vector_bundle
