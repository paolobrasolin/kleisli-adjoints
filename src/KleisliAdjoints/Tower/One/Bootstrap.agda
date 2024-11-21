{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.One.Bootstrap where

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
    O⊣C = KleisliAdjoints L⊣R

  kadjoint⇒monad : Monad (CoKleisli (adjoint⇒comonad L⊣R))
  kadjoint⇒monad = record
    { F = record
      { F₀ = F.F₀
      ; F₁ = λ {A} {_} f → F.F₁ f ∘ δ.η A ∘ ε.η (F.F₀ A)
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → id {F.F₀ X}
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → ε.η (F.F₀ X) ∘ ε.η (F.F₀ (F.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open D
          open S

  kadjoint⇒comonad : Comonad (Kleisli (adjoint⇒monad L⊣R))
  kadjoint⇒comonad = record
    { F = record
      { F₀ = F.F₀
      ; F₁ = λ {_} {B} f → η.η (F.F₀ B) ∘ μ.η B ∘ F.F₁ f
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = λ X → id {F.F₀ X}
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = λ X → η.η (F.F₀ (F.F₀ X)) ∘ η.η (F.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open C
          open T

  kContextualise : Functor (Kleisli (kadjoint⇒monad)) (CoKleisli (kadjoint⇒comonad))
  kContextualise = record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → R.F₁ (ϵ.η (L.F₀ (R.F₀ Y))) C.∘ R.F₁ (L.F₁ (R.F₁ f)) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ X)))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
          module η = NaturalTransformation (Adjoint.unit L⊣R)

  kOperationalise : Functor (CoKleisli (kadjoint⇒comonad)) (Kleisli (kadjoint⇒monad))
  kOperationalise = record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → L.F₁ (R.F₁ (ϵ.η (L.F₀ Y))) D.∘ L.F₁ (R.F₁ (L.F₁ f)) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ X)))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
          module η = NaturalTransformation (Adjoint.unit L⊣R)

  kKleisliAdjoints : kOperationalise ⊣ kContextualise
  kKleisliAdjoints = record
    { unit = record
      { η = λ X → η.η (R.F₀ (L.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → ϵ.η (L.F₀ (R.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
    where module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
          module η = NaturalTransformation (Adjoint.unit L⊣R)

