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

open import KleisliAdjoints using (Operationalise; Contextualise; KleisliAdjoints)
open import KleisliAdjoints.Tower.L1.Bootstrap using (kadjoint⇒monad; kadjoint⇒comonad; kOperationalise; kContextualise; kKleisliAdjoints)
open import KleisliAdjoints.Tower.L2.Bootstrap using (kkadjoint⇒monad; kkadjoint⇒comonad; kkOperationalise; kkContextualise; kkKleisliAdjoints)

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

  -- TODO: apparently `adjoint⇒monad (kkKleisliAdjoints L⊣R)` reduces much better than `kkadjoint⇒monad (O⊣C)`; I should revise Tower.L2.Fleshouts.

  _ : adjoint⇒monad (kkKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X)
      ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ (L.F₀ (R.F₀ X))) D.⇒ L.F₀ (R.F₀ Y)) → ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X)))) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))) }
      -- ε (L (R (L (R Y)))) ∘ L (η (R (L (R Y))) ∘ R f ∘ η (R (L (R X)))) ∘ ε (L (R (L (R X))))
      -- εLRLRY ∘ LηRLRY ∘ LRf ∘ LηRLRX ∘ εLRLRX
      -- εSSY ∘ δSY ∘ Sf ∘ δSX ∘ εSSX
      -- (εS SY ∘ δ SY) ∘ Sf ∘ (δSX ∘ εSSX)
      -- Sf ∘ (εS SSX ∘ δ SSX)
      -- Sf where  f : SSX → SY
    ; η = record
      { η = λ X → D.id }
    ; μ = record
      { η = λ X → ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))))) } }
      -- ε (L (R (L (R X)))) ∘ L 1 ∘ ε (L (R (L (R (L (R X))))))
      -- εLRLRX ∘ εLRLRLRX
      -- εSSX ∘ εSSSX
  _ = refl

  _ : adjoint⇒comonad (kkKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X)
      ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) }
      -- η (R (L (R (L Y)))) ∘ R (ε (L (R (L Y))) ∘ L f ∘ ε (L (R (L X)))) ∘ η (R (L (R (L X))))
      -- ηRLRLY ∘ RεLRLY ∘ RLf ∘ RεLRLX ∘ ηRLRLX
      -- ηTTY ∘ μTY ∘ Tf ∘ μTX ∘ ηTTX
      -- (ηTTY ∘ μTY) ∘ Tf ∘ (μ TX ∘ ηT TX)
      -- (μ Y ∘ ηT Y) ∘ Tf
      -- Tf  where  f : TX → TTY
    ; ε = record
      { η = λ X → C.id }
    ; δ = record
      { η = λ X → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) } }
      -- η (R (L (R (L (R (L X)))))) ∘ R 1 ∘ η (R (L (R (L X))))
      -- ηRLRLRLX ∘ ηRLRLX
      -- ηTTTX ∘ ηTTX
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

  _ : kContextualise (kKleisliAdjoints L⊣R) ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} → R.F₁ }
  _ = refl

  _ : kOperationalise (kKleisliAdjoints L⊣R) ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} → L.F₁ }
  _ = refl

  _ : kKleisliAdjoints (kKleisliAdjoints L⊣R) ≡ record
    { unit = record
      { η = λ X → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) }
      -- ηTTX
    ; counit = record
      { η = λ X → ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))) } }
      -- εSSX
  _ = refl

