{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.One.Fleshouts where

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
    module ε = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    O⊣C = KleisliAdjoints L⊣R

  _ : adjoint⇒monad (O⊣C) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X)
      -- SX
      ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ Y) → ε.η (L.F₀ (R.F₀ Y)) D.∘ L.F₁ (η.η (R.F₀ Y) C.∘ R.F₁ f C.∘ η.η (R.F₀ X)) D.∘ ε.η (L.F₀ (R.F₀ X)) }
      -- ε (L (R Y)) ∘ L (η (R Y) ∘ R f ∘ η (R X)) ∘ ε (L (R X))
      -- εLRY ∘ LηRY ∘ LRf ∘ LηRX ∘ εLRX
      -- εSY ∘ δY ∘ Sf ∘ δX ∘ εSX
      -- (εS Y ∘ δ Y) ∘ Sf ∘ (δX ∘ εSX)
      -- Sf ∘ (εS SX ∘ δ SX)
      -- Sf  where  f : SX → Y
    ; η = record
      { η = λ X → D.id }
      -- 1
    ; μ = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X)) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))) } }
      -- ε (L (R X)) ∘ L 1 ∘ ε (L (R (L (R X))))
      -- εLRX ∘ εLRLRX
      -- εSX ∘ εSSX
  _ = refl

  _ : adjoint⇒comonad (O⊣C) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X)
      -- TX
      ; F₁ = λ {X} {Y} (f : X C.⇒ R.F₀ (L.F₀ Y)) → η.η (R.F₀ (L.F₀ Y)) C.∘ R.F₁ (ε.η (L.F₀ Y) D.∘ L.F₁ f D.∘ ε.η (L.F₀ X)) C.∘ η.η (R.F₀ (L.F₀ X)) }
      -- η (R (L Y)) ∘ R (ε (L Y) ∘ L f ∘ ε (L X)) ∘ η (R (L X))
      -- ηRLY ∘ RεLY ∘ RLf ∘ RεLX ∘ ηRLX
      -- ηTY ∘ μY ∘ Tf ∘ μX ∘ ηTX
      -- (ηTY ∘ μY) ∘ Tf ∘ (μ X ∘ ηT X)
      -- (μ TY ∘ ηT TY) ∘ Tf
      -- Tf  where  f : X → TY
    ; ε = record
      { η = λ X → C.id }
      -- 1
    ; δ = record
      { η = λ X → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ X)) } }
      -- η (R (L (R (L X)))) ∘ R 1 ∘ η (R (L X))
      -- ηRLRLX ∘ ηRLX
      -- ηTTX ∘ ηTX
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

  _ : Contextualise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ Y))) C.∘ R.F₁ (L.F₁ C.id)) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ X)))) C.∘ C.id }
    -- (R (ε (L (R Y))) ∘ R (L 1)) ∘ (R (ε (L (R (L (R Y))))) ∘ R (L (η (R (L (R Y))) ∘ R f ∘ η (R X)))) ∘ 1
    -- RεLRY ∘ RεLRLRY ∘ RLηRLRY ∘ RLRf ∘ RLηRX
    -- RεSY ∘ RεSSY ∘ RδSY ∘ RSf ∘ RδX
    -- RεSY ∘ (R εS SY ∘ R δ SY) ∘ (R Sf ∘ R δX)
    -- (R εS Y ∘ R δ Y) ∘ Rf
    -- Rf  where  f : SX → SY
  _ = refl

  _ : Operationalise O⊣C ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → D.id D.∘ L.F₁ (R.F₁ ((ε.η (L.F₀ Y) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X)))) D.∘ L.F₁ (R.F₁ D.id) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ X))) }
    -- 1 ∘ L (R ((ε (L Y) ∘ L f ∘ ε (L (R (L X)))) ∘ L (R 1) ∘ L (η (R (L X))))) ∘ L (η (R (L X)))
    -- LRεLY ∘ LRLf ∘ LRεLRLX ∘ LRLηRLX ∘ LηRLX
    -- LμY ∘ LTf ∘ LμTX ∘ LTηTX ∘ LηTX
    -- (LμY ∘ LTf) ∘ (L μ TX ∘ L Tη TX) ∘ LηTX
    -- Lf ∘ (L μ X ∘ L ηT X)
    -- Lf  where  f : TX → TY
  _ = refl

  _ : KleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → η.η (R.F₀ (L.F₀ X)) }
      -- ηTX
    ; counit = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X)) }
      -- εSX
    }
  _ = refl

