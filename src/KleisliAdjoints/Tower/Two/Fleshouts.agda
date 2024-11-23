{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.Two.Fleshouts where

open import Level
open import Agda.Builtin.Equality using (_≡_; refl)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.Monad using (Monad)
open import Categories.Comonad using (Comonad)

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)
open import KleisliAdjoints.Tower.One.Bootstrap using (kadjoint⇒monad; kadjoint⇒comonad; kOperationalise; kContextualise; kKleisliAdjoints)

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
    O⊣C = KleisliAdjoints L⊣R

  _ : adjoint⇒monad (kKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X) -- TX
      ; F₁ = λ f → R.F₁ (L.F₁ f) } -- Tf
    ; η = record
      { η = λ X → η.η (R.F₀ (L.F₀ X)) } -- ηTX
    ; μ = record
      { η = λ X → R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ X)))) } -- μTX
    }
  _ = refl

  _ : adjoint⇒comonad (kKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X) -- SX
      ; F₁ = λ f → L.F₁ (R.F₁ f) } -- Sf
    ; ε = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X)) } -- εSX
    ; δ = record
      { η = λ X → L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))) } } -- δSX
  _ = refl

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module ε = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    O⊣C = KleisliAdjoints L⊣R

  _ : kContextualise O⊣C ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) → ε.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X))) }
    -- ε (L (R (L Y))) ∘ L f ∘ ε (L (R (L X)))
    -- εLRLY ∘ Lf ∘ εLRLX
    -- ϵLTY ∘ Lf ∘ ϵLTX where f : TX → TTY
  _ = refl

  _ : kOperationalise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ (L.F₀ (R.F₀ X))) D.⇒ L.F₀ (R.F₀ Y)) → η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X))) }
    -- η (R (L (R Y))) ∘ R f ∘ η (R (L (R X)))
    -- ηRLRY ∘ Rf ∘ ηRLRX
    -- ηRSY ∘ Rf ∘ ηRSX where f : SSX → SY
  _ = refl

  _ : kKleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → D.id }
    ; counit = record
      { η = λ X → C.id }
    }
  _ = refl

