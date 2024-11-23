{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.One.Bootstrap where

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

    -- NOTE: to get these we just open the (co)monad
    -- module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
    -- module η = NaturalTransformation (Adjoint.unit L⊣R)

  kadjoint⇒monad : Monad (CoKleisli (adjoint⇒comonad L⊣R))
  kadjoint⇒monad = record
    { F = record
      { F₀ = S.F₀
      ; F₁ = λ {X} {Y} (f : S.F₀ X ⇒ Y) → S.F₁ f
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → id {S.F₀ X}
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → ε.η (S.F₀ X) ∘ ε.η (S.F₀ (S.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open D
          open S renaming (F to S)

  kadjoint⇒comonad : Comonad (Kleisli (adjoint⇒monad L⊣R))
  kadjoint⇒comonad = record
    { F = record
      { F₀ = T.F₀
      ; F₁ = λ {X} {Y} (f : X ⇒ T.F₀ Y) → T.F₁ f
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = λ X → id {T.F₀ X}
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = λ X → η.η (T.F₀ (T.F₀ X)) ∘ η.η (T.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open C
          open T renaming (F to T)

  kContextualise : Functor (Kleisli (kadjoint⇒monad)) (CoKleisli (kadjoint⇒comonad))
  kContextualise = record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ X D.⇒ S.F₀ Y) → R.F₁ f
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open C
          open S renaming (F to S)

  kOperationalise : Functor (CoKleisli (kadjoint⇒comonad)) (Kleisli (kadjoint⇒monad))
  kOperationalise = record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : T.F₀ X C.⇒ T.F₀ Y) → L.F₁ f
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open D
          open T renaming (F to T)

  kKleisliAdjoints : kOperationalise ⊣ kContextualise
  kKleisliAdjoints = record
    { unit = record
      { η = λ X → η.η (T.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → ε.η (S.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
    where open T renaming (F to T)
          open S renaming (F to S)

