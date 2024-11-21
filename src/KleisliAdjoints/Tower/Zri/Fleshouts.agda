{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.Zri.Fleshouts where

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

open import KleisliAdjoints using (KleisliAdjoints)
open import KleisliAdjoints.Tower.Two.Bootstrap using (kkadjoint⇒monad; kkadjoint⇒comonad; kkOperationalise; kkContextualise; kkKleisliAdjoints)

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

  _ : kkadjoint⇒monad (O⊣C) ≡ record
    { F = record
      { F₀ = ?
      ; F₁ = ?
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
  _ = refl

  _ : kkadjoint⇒comonad (O⊣C) ≡ record
    { F = record
      { F₀ = ?
      ; F₁ = ?
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
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

  _ : kkContextualise O⊣C ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : kkOperationalise O⊣C ≡ record
    { F₀ = ?
    ; F₁ = ?
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : kkKleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = ?
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
  _ = refl

