{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.L0.Fleshouts where

open import Level
open import Agda.Builtin.Equality using (_≡_; refl)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Construction.CoKleisli using (Cofree) renaming (Forgetful to Coforgetful)
open import Categories.Adjoint.Construction.Kleisli using (Forgetful; Free)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module ε = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)

  _ : adjoint⇒monad (L⊣R) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X)
      -- TX
      ; F₁ = λ f → R.F₁ (L.F₁ f) }
      -- Tf
    ; η = record
      { η = λ X → η.η X }
      -- ηX
    ; μ = record
      { η = λ X → R.F₁ (ε.η (L.F₀ X)) } }
      -- μX
  _ = refl

  _ : Kleisli (adjoint⇒monad L⊣R) ≡ record
    { Obj = C.Obj
    ; _⇒_ = λ A B → A C.⇒ R.F₀ (L.F₀ B)
    -- A → TB
    ; _≈_ = C._≈_
    ; id = λ { {X} → η.η X }
    ; _∘_ = λ {A} {B} {C} f g → (R.F₁ (ε.η (L.F₀ C)) C.∘ R.F₁ (L.F₁ f)) C.∘ g }
    -- μX ∘ Tf ∘ g
    -- f* ∘ g
  _ = refl

  _ : Free (adjoint⇒monad L⊣R) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ { {A} {B} f → η.η B C.∘ f } }
    -- ηB ∘ f
  _ = refl

  _ : Forgetful (adjoint⇒monad L⊣R) ≡ record
    { F₀ = λ X → R.F₀ (L.F₀ X)
    -- TX
    ; F₁ = λ { {A} {B} f → R.F₁ (ε.η (L.F₀ B)) C.∘ R.F₁ (L.F₁ f) } }
    -- μB ∘ Tf
    -- f*
  _ = refl

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module ε = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)

  _ : adjoint⇒comonad (L⊣R) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X)
      -- SX
      ; F₁ = λ f → L.F₁ (R.F₁ f) }
      -- Sf
    ; ε = record
      { η = λ X → ε.η X }
      -- εX
    ; δ = record
      { η = λ X → L.F₁ (η.η (R.F₀ X)) } }
      -- δX
  _ = refl

  _ : CoKleisli (adjoint⇒comonad (L⊣R)) ≡ record
    { Obj = D.Obj
    ; _⇒_ = λ A B → L.F₀ (R.F₀ A) D.⇒ B
    -- SA → B
    ; _≈_ = D._≈_
    ; id = λ { {X} → ε.η X }
    ; _∘_ = λ {A} {B} {C} f g → f D.∘ L.F₁ (R.F₁ g) D.∘ L.F₁ (η.η (R.F₀ A)) }
    -- f ∘ Sg ∘ δA
    -- f ∘ gᵒ
  _ = refl

  _ : Cofree (adjoint⇒comonad L⊣R) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ { {A} {B} f → f D.∘ ε.η A } }
    -- f ∘ εA
  _ = refl

  _ : Coforgetful (adjoint⇒comonad L⊣R) ≡ record
    { F₀ = λ X → L.F₀ (R.F₀ X)
    -- SX
    ; F₁ = λ { {A} {B} f → L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ A)) } }
    -- Sf ∘ δA
    -- fᵒ
  _ = refl

