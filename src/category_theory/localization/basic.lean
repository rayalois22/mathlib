/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.construction
import category_theory.category_isomorphism

noncomputable theory

namespace category_theory

open category

variables {C D : Type*} [category C] [category D]
variables (L : C ⥤ D) (W : arrow_class C)
variables (E : Type*) [category E]

namespace functor

structure is_localization :=
(inverts_W : W.is_inverted_by L)
(is_equivalence : is_equivalence (localization.construction.lift L inverts_W))

structure is_strict_localization :=
(inverts_W : W.is_inverted_by L)
(is_isomorphism : is_category_isomorphism (localization.construction.lift L inverts_W))

namespace is_strict_localization

variables {L W}

def as_localization (h : L.is_strict_localization W) :
  L.is_localization W :=
{ inverts_W := h.inverts_W,
  is_equivalence := is_equivalence.of_equivalence
    h.is_isomorphism.to_category_isomorphism.as_equivalence, }

variables (L W)

structure universal_property_fixed_target :=
(inverts_W : W.is_inverted_by L)
(lift : Π (G : C ⥤ E) (hG : W.is_inverted_by G), D ⥤ E)
(fac : ∀ (G : C ⥤ E) (hG : W.is_inverted_by G), L ⋙ lift G hG = G)
(uniq : ∀ (G₁ G₂ : D ⥤ E), L ⋙ G₁ = L ⋙ G₂ → G₁ = G₂)

def universal_property_localization_fixed_target :
  universal_property_fixed_target (W.Q) W E :=
{ inverts_W := W.is_inverted_by_Q,
  lift := localization.construction.lift,
  fac := localization.construction.fac,
  uniq := localization.construction.uniq, }

variable {E}

def uniqueness_localization (F₁ : C ⥤ D) (F₂ : C ⥤ E)
  (L₁ : universal_property_fixed_target F₁ W E)
  (L₂ : universal_property_fixed_target F₂ W D)
  (L₁' : universal_property_fixed_target F₁ W D)
  (L₂' : universal_property_fixed_target F₂ W E) :
  category_isomorphism D E :=
{ functor := L₁.lift F₂ L₂.inverts_W,
  inverse := L₂.lift F₁ L₁.inverts_W,
  unit_eq := begin
    apply L₁'.uniq,
    rw [← functor.assoc, L₁.fac, L₂.fac, functor.comp_id],
  end,
  counit_eq := begin
    apply L₂'.uniq,
    rw [← functor.assoc, L₂.fac, L₁.fac, functor.comp_id],
  end, }

def mk'
  (h₁ : universal_property_fixed_target L W W.localization)
  (h₂ : universal_property_fixed_target L W D) :
  is_strict_localization L W :=
{ inverts_W := h₁.inverts_W,
  is_isomorphism := is_category_isomorphism.of_category_isomorphism
    (uniqueness_localization W W.Q L
    (universal_property_localization_fixed_target W D) h₁
    (universal_property_localization_fixed_target W W.localization) h₂), }

variables {L W}
variable (hL : is_strict_localization L W)

def lift (F : C ⥤ E) (hF : W.is_inverted_by F) : D ⥤ E :=
hL.is_isomorphism.inverse ⋙ localization.construction.lift F hF

lemma fac (F : C ⥤ E) (hF : W.is_inverted_by F) :
  L ⋙ hL.lift F hF = F :=
begin
  dsimp [lift],
  rw ← functor.assoc,
  conv_lhs { congr, congr, rw ← localization.construction.fac L hL.inverts_W, },
  rw [functor.assoc W.Q, ← hL.is_isomorphism.unit_eq,
    functor.comp_id, localization.construction.fac],
end

include hL

lemma uniq (F₁ F₂ : D ⥤ E) (eq : L ⋙ F₁ = L ⋙ F₂) : F₁ = F₂ :=
begin
  rw [← localization.construction.fac L hL.inverts_W, functor.assoc, functor.assoc] at eq,
  rw [← functor.id_comp F₁, ← functor.id_comp F₂, ← hL.is_isomorphism.counit_eq,
    functor.assoc, functor.assoc, localization.construction.uniq _ _ eq],
end

def inv (w : W) : L.obj (w.1.right) ⟶ L.obj (w.1.left) :=
begin
  haveI : is_iso (L.map w.1.hom) := hL.inverts_W w,
  exact category_theory.inv (L.map w.val.hom),
end

def obj_equiv : C ≃ D :=
(localization.construction.obj_equiv W).trans
hL.is_isomorphism.to_category_isomorphism.obj_equiv

@[simp]
lemma obj_equiv_to_fun (X : C) : hL.obj_equiv.to_fun X = L.obj X :=
begin
  dsimp [obj_equiv],
  simpa only [category_isomorphism.obj_equiv_apply, localization.construction.lift_obj,
    is_category_isomorphism.to_category_isomorphism_functor],
end

lemma arrow_class_is_univ
  (A : arrow_class D)
  (hA₁ : ∀ (f : arrow C), L.map_arrow.obj f ∈ A)
  (hA₂ : ∀ (w : W), arrow.mk (hL.inv w) ∈ A)
  (hA₃ : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : arrow.mk f ∈ A) (hg : arrow.mk g ∈ A),
    arrow.mk (f ≫ g) ∈ A) : A = set.univ :=
begin
  ext f,
  split,
  { intro hf,
    apply set.mem_univ, },
  { intro hf,
    clear hf,
    cases hL.is_isomorphism.to_category_isomorphism.arrow_equiv.surjective f with g hg,
    simp only [category_isomorphism.arrow_equiv_apply,
      is_category_isomorphism.to_category_isomorphism_functor] at hg,
    subst hg,
    let F := localization.construction.lift L hL.inverts_W,
    let G : _ ⥤ W.localization := quotient.functor _,
    suffices : ∀ (X₁ X₂ : C) (p : localization.construction.ι_paths W X₁ ⟶
      localization.construction.ι_paths W X₂), arrow.mk (F.map (G.map p)) ∈ A,
    { rcases g with ⟨⟨⟨X⟩⟩, ⟨⟨Y⟩⟩, g⟩,
      dsimp at g,
      convert this _ _ (G.preimage g),
      erw full.witness,
      refl, },
    intros X₁ X₂ p,
    induction p with X₂ X₃ p f hp,
    { simpa only [map_arrow_obj_arrow_mk, L.map_id] using hA₁ (arrow.mk (𝟙 X₁)), },
    { let φ : (_ : paths (localization.construction.loc_quiver W)) ⟶ _ := p,
      rw [show p.cons f = φ ≫ quiver.hom.to_path f, by refl],
      simp only [functor.map_comp],
      apply hA₃ _ _ hp,
      rcases f with (f|⟨f, hf⟩),
      { dsimp,
        simpa only [compose_path_to_path, map_arrow_obj_arrow_mk] using hA₁ (arrow.mk f), },
      { dsimp,
        simpa only [compose_path_to_path] using hA₂ ⟨_, hf⟩, }, }, },
end

lemma arrow_class_is_univ'
  (A : arrow_class D)
  (hA₁ : ∀ {X Y : C} (f : X ⟶ Y), arrow.mk (L.map f) ∈ A)
  (hA₂ : ∀ {X Y : D} (e : X ≅ Y), arrow.mk e.hom ∈ A → arrow.mk e.inv ∈ A)
  (hA₃ : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : arrow.mk f ∈ A) (hg : arrow.mk g ∈ A),
  arrow.mk (f ≫ g) ∈ A) : A = set.univ :=
begin
  apply hL.arrow_class_is_univ,
  { intro f,
    exact hA₁ f.hom, },
  { intro w,
    haveI : is_iso (L.map (w.1.hom)) := hL.inverts_W w,
    apply hA₂ (as_iso (L.map (w.1.hom))),
    exact hA₁ w.1.hom, },
  { intros X Y Z,
    exact hA₃, },
end

end is_strict_localization

end functor

def naturality_condition {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) : arrow_class C :=
λ w, F.map w.hom ≫ app w.right = app w.left ≫ G.map w.hom

namespace naturality_condition

lemma iff {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) {X Y : C} (f : X ⟶ Y) :
  arrow.mk f ∈ naturality_condition app ↔ (F.map f ≫ app Y = app X ≫ G.map f) := by refl

lemma inv {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) (X Y : C) (e : X ≅ Y)
(he : arrow.mk e.hom ∈ naturality_condition app) : arrow.mk e.inv ∈ naturality_condition app :=
begin
  rw iff at ⊢ he,
  rw [← cancel_mono (G.map e.hom), assoc, ← he, ← assoc, ← F.map_comp,
    assoc, ← G.map_comp, e.inv_hom_id, F.map_id, G.map_id, id_comp, comp_id],
end

lemma comp {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
(hf : arrow.mk f ∈ naturality_condition app) (hg : arrow.mk g ∈ naturality_condition app) :
  arrow.mk (f ≫ g) ∈ naturality_condition app :=
begin
  rw iff at ⊢ hf hg,
  rw [F.map_comp, G.map_comp, assoc, hg, ← assoc, hf, assoc],
end

end naturality_condition

namespace functor

namespace is_strict_localization

variables {L W E}
variable (hL : is_strict_localization L W)
include hL

namespace nat_trans_extension

variables {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G)
include τ

def app (X : D) : F.obj X ⟶ G.obj X :=
begin
  have eq := λ X, (hL.obj_equiv.right_inv X).symm,
  simp only [hL.obj_equiv_to_fun] at eq,
  refine eq_to_hom _ ≫ τ.app (hL.obj_equiv.inv_fun X) ≫ eq_to_hom _,
  { congr,
    apply eq, },
  { symmetry,
    congr,
    apply eq, },
end

@[simp]
lemma app_eq (X : C) : (app hL τ) (L.obj X) = τ.app X :=
begin
  dsimp only [app],
  have eq := hL.obj_equiv.left_inv X,
  simp only [obj_equiv_to_fun] at eq,
  have h := τ.naturality (eq_to_hom eq),
  simp only [eq_to_hom_map] at h,
  erw ← h,
  simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp],
end

end nat_trans_extension

@[simps]
def nat_trans_extension {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) :
  F ⟶ G :=
begin
  have h := arrow_class_is_univ' hL (naturality_condition (nat_trans_extension.app hL τ)) _
    (naturality_condition.inv _) (naturality_condition.comp _), rotate,
  { intros X Y f,
    simp only [naturality_condition.iff, nat_trans_extension.app_eq],
    exact τ.naturality f, },
  exact
  { app := nat_trans_extension.app hL τ,
    naturality' := λ X Y f, begin
      have hf : arrow.mk f ∈ naturality_condition (nat_trans_extension.app hL τ),
      { rw h,
        apply set.mem_univ, },
      exact hf,
    end, }
end

@[simp]
lemma nat_trans_extension_hcomp {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) :
  (𝟙 L) ◫ nat_trans_extension hL τ = τ :=
begin
  ext X,
  simp only [nat_trans.hcomp_app, nat_trans_extension_app, nat_trans_extension.app_eq,
    nat_trans.id_app, map_id, comp_id],
end

end is_strict_localization

end functor

namespace arrow_class

@[derive category]
def functors_inverting := { F : C ⥤ E // W.is_inverted_by F}

end arrow_class

namespace functor

namespace is_strict_localization

variables {L W}

variable (hL : is_strict_localization L W)

include hL

@[simps]
def whiskering_left_functor (E : Type*) [category E] :
  (D ⥤ E) ⥤ (W.functors_inverting E) :=
begin
  refine full_subcategory.lift _ ((whiskering_left _ _ E).obj L) _,
  intro F,
  exact arrow_class.is_inverted_by.of_comp W L F hL.inverts_W,
end

lemma nat_trans_hcomp_injective {E : Type*} [category E] {F G : D ⥤ E} (τ₁ τ₂ : F ⟶ G)
  (h : 𝟙 L ◫ τ₁ = 𝟙 L ◫ τ₂) : τ₁ = τ₂ :=
begin
  ext X,
  have eq := hL.obj_equiv.right_inv X,
  simp only [obj_equiv_to_fun] at eq,
  rw [← eq, ← nat_trans.id_hcomp_app, ← nat_trans.id_hcomp_app, h],
end

@[simps]
def whiskering_left_inverse (E : Type*) [category E] :
  (W.functors_inverting E) ⥤ (D ⥤ E) :=
{ obj := λ G, hL.lift G.1 G.2,
  map := λ G₁ G₂ τ, hL.nat_trans_extension
    (eq_to_hom (by rw hL.fac) ≫ τ ≫ eq_to_hom (by rw hL.fac)),
  map_id' := λ G, begin
    apply hL.nat_trans_hcomp_injective,
    simp only [nat_trans_extension_hcomp],
    erw [id_comp, eq_to_hom_trans, eq_to_hom_refl],
    tidy,
  end,
  map_comp' := λ G₁ G₂ G₃ τ₁ τ₂, begin
    apply hL.nat_trans_hcomp_injective,
    simp only [nat_trans_extension_hcomp, nat_trans.hcomp_comp, assoc,
      eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp],
    erw assoc,
  end }

def whiskering_left_category_isomorphism (E : Type*) [category E] :
  category_isomorphism (D ⥤ E) (W.functors_inverting E) :=
{ functor := hL.whiskering_left_functor E,
  inverse := hL.whiskering_left_inverse E,
  unit_eq := begin
    apply functor.ext,
    { intros G₁ G₂ τ,
      apply hL.nat_trans_hcomp_injective,
      ext X,
      simp only [id_map, nat_trans.hcomp_app, nat_trans.id_app, map_id, comp_map,
        whiskering_left_inverse_map, nat_trans.hcomp_comp, nat_trans_extension_hcomp,
        assoc, nat_trans.comp_app, eq_to_hom_app, whiskering_left_functor_map_app,
        eq_to_hom_refl, eq_to_hom_trans_assoc, id_comp], },
    { intro F,
      simp only [comp_obj, whiskering_left_inverse_obj],
      apply hL.uniq,
      rw hL.fac,
      refl, },
  end,
  counit_eq := begin
    apply functor.ext,
    { rintros ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩ φ,
      ext X,
      dsimp,
      rw nat_trans_extension.app_eq,
      refl, },
    { rintro ⟨F, hF⟩,
      ext,
      exact hL.fac F hF, },
  end, }

end is_strict_localization

end functor

end category_theory
