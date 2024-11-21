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
      ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ Y) → ε.η (L.F₀ (R.F₀ Y)) D.∘ L.F₁ (η.η (R.F₀ Y) C.∘ R.F₁ f C.∘ η.η (R.F₀ X)) D.∘ ε.η (L.F₀ (R.F₀ X))
      -- ε (L (R Y)) ∘ L (η (R Y) ∘ R f ∘ η (R X)) ∘ ε (L (R X))
      -- εLRY ∘ LηRY ∘ LRf ∘ LηRX ∘ εLRX
      -- εSY ∘ δY ∘ Sf ∘ δX ∘ εSX
      -- (εS Y ∘ δ Y) ∘ Sf ∘ δX ∘ εSX
      -- Sf ∘ δX ∘ εSX  where  f : SX → Y
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → D.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X)) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))
      -- ε (L (R X)) ∘ L 1 ∘ ε (L (R (L (R X))))
      -- εLRX ∘ εLRLRX
      -- εSX ∘ εSSX
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
  _ = refl

  _ : adjoint⇒comonad (O⊣C) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X)
      ; F₁ = λ {X} {Y} (f : X C.⇒ R.F₀ (L.F₀ Y)) → η.η (R.F₀ (L.F₀ Y)) C.∘ R.F₁ (ε.η (L.F₀ Y) D.∘ L.F₁ f D.∘ ε.η (L.F₀ X)) C.∘ η.η (R.F₀ (L.F₀ X))
      -- η (R (L Y)) ∘ R (ε (L Y) ∘ L f ∘ ε (L X)) ∘ η (R (L X))
      -- ηRLY ∘ RεLY ∘ RLf ∘ RεLX ∘ ηRLX
      -- ηTY ∘ μY ∘ Tf ∘ μX ∘ ηTX
      -- ηTY ∘ μY ∘ Tf ∘ (μ X ∘ ηT X)
      -- ηTY ∘ μY ∘ Tf  where  f : X → TY
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = λ X → C.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = λ X → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ X))
      -- η (R (L (R (L X)))) ∘ R 1 ∘ η (R (L X))
      -- ηRLRLX ∘ ηRLX
      -- ηTTX ∘ ηTX
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

  _ : Contextualise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ Y))) C.∘ R.F₁ (L.F₁ C.id)) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ X)))) C.∘ C.id
    -- (R (ε (L (R Y))) ∘ R (L 1)) ∘ (R (ε (L (R (L (R Y))))) ∘ R (L (η (R (L (R Y))) ∘ R f ∘ η (R X)))) ∘ 1
    -- RεLRY ∘ RεLRLRY ∘ RLηRLRY ∘ RLRf ∘ RLηRX
    -- RεSY ∘ RεSSY ∘ RδSY ∘ RSf ∘ RδX
    -- RεSY ∘ (R εS SY ∘ R δ SY) ∘ RSf ∘ RδX
    -- RεSY ∘ RSf ∘ RδX  where  f : SX → SY
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Operationalise O⊣C ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → D.id D.∘ L.F₁ (R.F₁ ((ε.η (L.F₀ Y) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X)))) D.∘ L.F₁ (R.F₁ D.id) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ X)))
    -- 1 ∘ L (R ((ε (L Y) ∘ L f ∘ ε (L (R (L X)))) ∘ L (R 1) ∘ L (η (R (L X))))) ∘ L (η (R (L X)))
    -- LRεLY ∘ LRLf ∘ LRεLRLX ∘ LRLηRLX ∘ LηRLX
    -- LμY ∘ LTf ∘ LμTX ∘ LTηTX ∘ LηTX
    -- LμY ∘ LTf ∘ (L μ TX ∘ L Tη TX) ∘ LηTX
    -- LμY ∘ LTf ∘ LηTX  where  f : TX → TY
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : KleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → η.η (R.F₀ (L.F₀ X))
      -- ηTX
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X))
      -- εSX
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
  _ = refl

