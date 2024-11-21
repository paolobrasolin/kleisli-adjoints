{-# OPTIONS --without-K --allow-unsolved-metas #-}
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

open import KleisliAdjoints using (Operationalise; Contextualise; KleisliAdjoints)
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

  _ : kadjoint⇒monad (O⊣C) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X)
      -- TX
      ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ Y)) C.∘ R.F₁ (ε.η (L.F₀ Y) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))))) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ X))))) C.∘ C.id
      -- (R (ε (L (R (L Y)))) ∘ R (L (η (R (L Y)) ∘ R (ε (L Y) ∘ L f ∘ ε (L (R (L X)))) ∘ η (R (L (R (L X))))))) ∘ (R (ε (L (R (L (R (L X)))))) ∘ R (L (η (R (L (R (L X)))) ∘ R 1 ∘ η (R (L X))))) ∘ 1
      -- RεLRLY ∘ RLηRLY ∘ RLRεLY ∘ RLRLf ∘ RLRεLRLX ∘ RLηRLRLX ∘ RεLRLRLX ∘ RLηRLRLX ∘ RLηRLX
      -- μTY ∘ TηTY ∘ TμY ∘ TTf ∘ TμTX ∘ TηTTX ∘ μTTX ∘ TηTTX ∘ TηTX
      -- (μ TY ∘ Tη TY) ∘ TμY ∘ TTf ∘ (T μ TX ∘ T ηT TX) ∘ (μ TTX ∘ Tη TTX) ∘ TηTX
      -- TμY ∘ TTf ∘ TηTX where f : TX → TY
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → η.η (R.F₀ (L.F₀ X))
      -- η (R (L X))
      -- ηRLX
      -- ηTX
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ (L.F₁ C.id)) C.∘ C.id
      -- (R (ε (L (R (L X)))) ∘ R (L 1)) ∘ 1
      -- RεLRLX
      -- μTX
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
  _ = refl

  _ : kadjoint⇒comonad (O⊣C) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X)
      ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → D.id D.∘ L.F₁ (R.F₁ ((ε.η (L.F₀ (R.F₀ Y)) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) D.∘ L.F₁ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ X)) D.∘ ε.η (L.F₀ (R.F₀ X)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X))))
      -- 1 ∘ L (R ((ε (L (R Y)) ∘ L 1 ∘ ε (L (R (L (R Y))))) ∘ L (R (ε (L (R (L (R Y)))) ∘ L (η (R (L (R Y))) ∘ R f ∘ η (R X)) ∘ ε (L (R X)))) ∘ L (η (R (L (R X)))))) ∘ L (η (R (L (R X))))
      -- LRεLRY ∘ LRεLRLRY ∘ LRLRεLRLRY ∘ LRLRLηRLRY ∘ LRLRLRf ∘ LRLRLηRX ∘ LRLRεLRX ∘ LRLηRLRX ∘ LηRLRX
      -- SεSY ∘ SεSSY ∘ SSεSSY ∘ SSδSY ∘ SSSf ∘ SSδX ∘ SSεSX ∘ SδSX ∘ δSX
      -- SεSY ∘ SεSSY ∘ (SS εS SY ∘ SS δ SY) ∘ SSSf ∘ SSδX ∘ (S Sε SX ∘ S δ SX) ∘ δSX
      -- SεSY ∘ (S εSSY ∘ S SSf) ∘ SSδX ∘ δSX
      -- SεSY ∘ SSf ∘ (S εSSX ∘ S SδX) ∘ δSX
      -- SεSY ∘ SSf ∘ SδX ∘ (Sε SX ∘ δ SX)
      -- SεSY ∘ SSf ∘ SδX  where  f : SX → SY
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; ε = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X))
      -- ε (L (R X))
      -- εLRX
      -- εSX
      ; commute = {! !} ; sym-commute = {! !} }
    ; δ = record
      { η = λ X → D.id D.∘ L.F₁ (R.F₁ D.id) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X))))
      -- 1 ∘ L (R 1) ∘ L (η (R (L (R X))))
      -- LηRLRX
      -- δSX
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

  _ : kContextualise O⊣C ≡ record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) → (ε.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))))) D.∘ L.F₁ (R.F₁ ((ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))) D.∘ L.F₁ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ X))) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X))))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))
    -- (ε (L (R (L Y))) ∘ L 1 ∘ ε (L (R (L (R (L Y)))))) ∘ L (R ((ε (L (R (L (R (L Y))))) ∘ L (η (R (L (R (L Y)))) ∘ R (ε (L (R (L Y))) ∘ L f ∘ ε (L (R (L X)))) ∘ η (R (L (R (L X))))) ∘ ε (L (R (L (R (L X)))))) ∘ L (R (ε (L (R (L (R (L X))))) ∘ L (η (R (L (R (L X)))) ∘ R 1 ∘ η (R (L X))) ∘ ε (L (R (L X))))) ∘ L (η (R (L (R (L X))))))) ∘ L (η (R (L (R (L X)))))
    -- εLRLY ∘ εLRLRLY ∘ LRεLRLRLY ∘ LRLηRLRLY ∘ LRLRεLRLY ∘ LRLRLf ∘ LRLRεLRLX ∘ LRLηRLRLX ∘ LRεLRLRLX ∘ LRLRεLRLRLX ∘ LRLRLηRLRLX ∘ LRLRLηRLX ∘ LRLRεLRLX ∘ LRLηRLRLX ∘ LηRLRLX
    -- εLTY ∘ εLTTY ∘ LμTTY ∘ LTηTTY ∘ LTμTY ∘ LTTf ∘ LTμTX ∘ LTηTTX ∘ LμTTX ∘ LTμTTX ∘ LTTηTTX ∘ LTTηTX ∘ LTμTX ∘ LTηTTX ∘ LηTTX
    -- εLTY ∘ εLTTY ∘ (L μ TTY ∘ L Tη TTY) ∘ LTμTY ∘ LTTf ∘ (LT μ TX ∘ LT ηT TX) ∘ LμTTX ∘ (LT μ TTX ∘ LT Tη TTX) ∘ LTTηTX ∘ (LT μ TX ∘ LT ηT TX) ∘ LηTTX
    -- ϵLTY ∘ (ϵLTTY ∘ LTμTY ∘ LTTf) ∘ (LμTTX ∘ LTTηTX) ∘ LηTTX
    -- ϵLTY ∘ Lf ∘ ϵLTX ∘ (LTμX ∘ LμTTX ∘ LTTηTX ∘ LηTTX)
    -- ϵLTY ∘ Lf ∘ ϵLTX ∘ (LT μ X ∘ LT Tη X ∘ L μ TX ∘ L ηT TX)
    -- ϵLTY ∘ Lf ∘ ϵLTX where f : TX → TTY
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : kOperationalise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ (L.F₀ (R.F₀ X))) D.⇒ L.F₀ (R.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ (ε.η (L.F₀ (R.F₀ Y)) D.∘ L.F₁ C.id D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))))))) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) C.∘ R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X)))) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))) C.∘ R.F₁ D.id C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X)))
    -- (R (ε (L (R (L (R Y))))) ∘ R (L (η (R (L (R Y))) ∘ R (ε (L (R Y)) ∘ L 1 ∘ ε (L (R (L (R Y))))) ∘ η (R (L (R (L (R Y)))))))) ∘ (R (ε (L (R (L (R (L (R Y))))))) ∘ R (L (η (R (L (R (L (R Y))))) ∘ R (ε (L (R (L (R Y)))) ∘ L (η (R (L (R Y))) ∘ R f ∘ η (R (L (R X)))) ∘ ε (L (R (L (R X))))) ∘ η (R (L (R (L (R X)))))))) ∘ η (R (L (R (L (R X))))) ∘ R 1 ∘ η (R (L (R X)))
    -- RεLRLRY ∘ RLηRLRY ∘ RLRεLRY ∘ RLRεLRLRY ∘ RLηRLRLRY ∘ RεLRLRLRY ∘ RLηRLRLRY ∘ RLRεLRLRY ∘ RLRLηRLRY ∘ RLRLRf ∘ RLRLηRLRX ∘ RLRεLRLRX ∘ RLηRLRLRX ∘ ηRLRLRX ∘ ηRLRX
    -- RεSSY ∘ RδSY ∘ RSεSY ∘ RSεSSY ∘ RδSSY ∘ RεSSSY ∘ RδSSY ∘ RSεSSY ∘ RSδSY ∘ RSSf ∘ RSδSX ∘ RSεSSX ∘ RδSSX ∘ ηRSSX ∘ ηRSX
    -- (R εS SY ∘ R δ SY) ∘ RSεSY ∘ (R Sε SSY ∘ R δ SSY) ∘ (R εS SSY ∘ R δ SSY) ∘ (RS εS SY ∘ RS δ SY) ∘ RSSf ∘ RSδSX ∘ (R Sε SSX ∘ R δ SSX) ∘ ηRSSX ∘ ηRSX
    -- RSεSY ∘ RSSf ∘ RSδSX ∘ ηRSSX ∘ ηRSX
    -- (RS f ∘ RS ϵSSX) ∘ RSδSX ∘ ηRSSX ∘ ηRSX
    -- RSf ∘ (RS ϵS SX ∘ RS δ SX) ∘ ηRSSX ∘ ηRSX
    -- (RSf ∘ ηRSSX) ∘ ηRSX
    -- ηRSY ∘ Rf ∘ ηRSX where f : SSX → SY
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : kKleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → D.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → C.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
  _ = refl

