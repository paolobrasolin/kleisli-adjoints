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

  _ : Op1 ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Op3 ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Co1 ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Co3 ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl
