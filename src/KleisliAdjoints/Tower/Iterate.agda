{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.Iterate where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.Monad using (Monad)
open import Categories.Comonad using (Comonad)
open import Agda.Builtin.Equality using (_≡_; refl)

open import KleisliAdjoints using (Operationalise; Contextualise; KleisliAdjoints)
open import KleisliAdjoints.Tower.Bootstrap using (kOperationalise; kContextualise; kKleisliAdjoints)

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
    module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    module S = Comonad (adjoint⇒comonad L⊣R)
    module T = Monad (adjoint⇒monad L⊣R)

    Op1 = Operationalise L⊣R
    Co1 = Contextualise L⊣R
    O⊣C = KleisliAdjoints L⊣R

    Op2 = kOperationalise L⊣R
    Co2 = kContextualise L⊣R
    KA2 = kKleisliAdjoints L⊣R

    Op3 = kOperationalise O⊣C
    Co3 = kContextualise O⊣C
    KA3 = kKleisliAdjoints O⊣C

  -- Ok, overall doing the following is much simpler: almost instantaneous and much simpler terms.

  _ : Op1 ≡ record
    { F₀ = R.F₀
    ; F₁ = λ f → η.η (R.F₀ _) C.∘ R.F₁ f C.∘ η.η (R.F₀ _)
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Op3 ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} f → (R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ Y)) D.∘ L.F₁ C.id D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))))))) C.∘ (R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X)))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X)))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Co1 ≡ record
    { F₀ = L.F₀
    ; F₁ = λ f → ϵ.η (L.F₀ _) D.∘ L.F₁ f D.∘ ϵ.η (L.F₀ _)
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Co3 ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} f → (ϵ.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ C.id D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))))) D.∘ L.F₁ (R.F₁ ((ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ f D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))) D.∘ L.F₁ (R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ X))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl
