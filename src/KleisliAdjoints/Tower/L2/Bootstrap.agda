{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.L2.Bootstrap where

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
open import Categories.Monad using (Monad)
open import Categories.Comonad using (Comonad)

open import KleisliAdjoints using (KleisliAdjoints)
open import KleisliAdjoints.Tower.L1.Bootstrap using (kadjoint⇒monad; kadjoint⇒comonad; kOperationalise; kContextualise; kKleisliAdjoints)

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

  kkadjoint⇒monad : Monad (CoKleisli (kadjoint⇒comonad L⊣R))
  kkadjoint⇒monad = record
    { F = record
      { F₀ = T.F₀
      ; F₁ = λ {X} {Y} (f : T.F₀ X ⇒ T.F₀ Y) → T.F₁ f
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → η.η (T.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → μ.η (T.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open C
          open T renaming (F to T)

  -- TODO: kkKleisli

  -- NOTE: this is the type of `Free kkadjoint⇒monad`
  kkFree : Functor (CoKleisli (kadjoint⇒comonad L⊣R)) (Kleisli kkadjoint⇒monad)
  kkFree = record
    { F₀ = λ X → X
    ; F₁ = λ {X} {Y} (f : T.F₀ X ⇒ T.F₀ Y) → η.η (T.F₀ Y) ∘ f
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open C
          open T renaming (F to T)

  -- NOTE: this is the type of `Forgetful kkadjoint⇒monad`
  kkForgetful : Functor (Kleisli kkadjoint⇒monad) (CoKleisli (kadjoint⇒comonad L⊣R))
  kkForgetful = record
    { F₀ = T.F₀
    ; F₁ = λ {X} {Y} (f : T.F₀ X ⇒ T.F₀ (T.F₀ Y)) → μ.η (T.F₀ Y) ∘ (T.F₁ f)
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open C
          open T renaming (F to T)

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module S = Comonad (adjoint⇒comonad L⊣R)
    module T = Monad (adjoint⇒monad L⊣R)

  kkadjoint⇒comonad : Comonad (Kleisli (kadjoint⇒monad L⊣R))
  kkadjoint⇒comonad = record
    { F = record
      { F₀ = S.F₀
      ; F₁ = λ {X} {Y} (f : S.F₀ X ⇒ S.F₀ Y) → S.F₁ f
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = λ X → ε.η (S.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = λ X → δ.η (S.F₀ X)
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
    where open D
          open S renaming (F to S)

  -- TODO: kkCoKleisli

  -- NOTE: this is the type of `Cofree kkadjoint⇒comonad`
  kkCofree : Functor (Kleisli (kadjoint⇒monad L⊣R)) (CoKleisli kkadjoint⇒comonad)
  kkCofree = record
    { F₀ = λ X → X
    ; F₁ = λ {X} {Y} (f : S.F₀ X ⇒ S.F₀ Y) → f ∘ ε.η (S.F₀ X)
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open D
          open S renaming (F to S)

  -- NOTE: this is the type of `Coforgetful kkadjoint⇒comonad`
  kkCoforgetful : Functor (CoKleisli kkadjoint⇒comonad) (Kleisli (kadjoint⇒monad L⊣R))
  kkCoforgetful = record
    { F₀ = S.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ (S.F₀ X) ⇒ S.F₀ Y) → S.F₁ f ∘ δ.η (S.F₀ X)
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open D
          open S renaming (F to S)

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module S = Comonad (adjoint⇒comonad L⊣R)
    module T = Monad (adjoint⇒monad L⊣R)

  kkContextualise : Functor (Kleisli (kkadjoint⇒monad L⊣R)) (CoKleisli (kkadjoint⇒comonad L⊣R))
  kkContextualise = record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : T.F₀ X C.⇒ T.F₀ (T.F₀ Y)) → ε.η (L.F₀ (T.F₀ Y)) ∘ L.F₁ f ∘ ε.η (L.F₀ (T.F₀ X))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open D
          open S using (ε)
          open T renaming (F to T)

  kkOperationalise : Functor (CoKleisli (kkadjoint⇒comonad L⊣R)) (Kleisli (kkadjoint⇒monad L⊣R))
  kkOperationalise = record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ (S.F₀ X) D.⇒ S.F₀ Y) → η.η (R.F₀ (S.F₀ Y)) ∘ R.F₁ f ∘ η.η (R.F₀ (S.F₀ X))
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    where open C
          open T using (η)
          open S renaming (F to S)

  kkKleisliAdjoints : kkOperationalise ⊣ kkContextualise
  kkKleisliAdjoints = record
    { unit = record
      { η = λ X → D.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → C.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }

