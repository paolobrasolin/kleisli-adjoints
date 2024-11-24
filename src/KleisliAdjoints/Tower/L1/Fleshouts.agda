{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.L1.Fleshouts where

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

open import KleisliAdjoints using (Operationalise; Contextualise; KleisliAdjoints)
open import KleisliAdjoints.Tower.L1.Bootstrap using (kadjoint⇒monad; kadjoint⇒comonad)

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

  _ : Kleisli (kadjoint⇒monad (L⊣R)) ≡ record
    { Obj = D.Obj
    ; _⇒_ = λ X Y → L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)
    -- L (R X) ⇒ L (R Y)
    -- SX ⇒ SY
    ; _≈_ = D._≈_
    ; id = D.id
    ; _∘_ = λ {X} {Y} {Z} f g → ((ε.η (L.F₀ (R.F₀ Z)) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Z))))) D.∘ L.F₁ (R.F₁ (L.F₁ (R.F₁ f))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))))) D.∘ L.F₁ (R.F₁ g) D.∘ L.F₁ (η.η (R.F₀ X))
    -- ((ε (L (R Z)) ∘ ε (L (R (L (R Z))))) ∘ L (R (L (R f))) ∘ L (η (R (L (R Y))))) ∘ L (R g) ∘ L (η (R X))
    -- εLRZ ∘ εLRLRZ ∘ LRLRf ∘ LηRLRY ∘ LRg ∘ LηRX
    -- εSZ ∘ εSSZ ∘ (SSf ∘ δSY) ∘ Sg ∘ δX
    -- εSZ ∘ (εS SZ ∘ δ SZ) ∘ S(f ∘ g) ∘ δX
    -- (εSZ ∘ S(f ∘ g)) ∘ δX
    -- (f ∘ g) ∘ (εS X ∘ δ X)
    -- f ∘ g
    ; assoc = {! !}
    ; sym-assoc = {! !}
    ; identityˡ = {! !}
    ; identityʳ = {! !}
    ; identity² = {! !}
    ; equiv = D.equiv
    ; ∘-resp-≈ = {! !}
    }
  _ = refl

  _ : Free (kadjoint⇒monad (L⊣R)) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ Y) → D.id D.∘ L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ X)) }
    -- 1 ∘ L (R f) ∘ L (η (R X))
    -- LRf ∘ LηRX
    -- Sf ∘ δX  where  f : SX → Y
  _ = refl

  _ : Forgetful (kadjoint⇒monad (L⊣R)) ≡ record
    { F₀ = λ X → L.F₀ (R.F₀ X)
    -- SX
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → (ε.η (L.F₀ (R.F₀ Y)) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) D.∘ L.F₁ (R.F₁ (L.F₁ (R.F₁ f))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))) }
    -- (ε (L (R Y)) ∘ ε (L (R (L (R Y))))) ∘ L (R (L (R f))) ∘ L (η (R (L (R X))))
    -- εLRY ∘ εLRLRY ∘ LRLRf ∘ LηRLRX
    -- εSY ∘ εSSY ∘ (SSf ∘ δSX)
    -- εSY ∘ (εS SY ∘ δ SY) ∘ Sf
    -- (εSY ∘ Sf)
    -- f ∘ εSX  where  f : SX → SY
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

  _ : CoKleisli (kadjoint⇒comonad (L⊣R)) ≡ record
    { Obj = C.Obj
    ; _⇒_ = λ X Y → R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)
    -- R (L X) ⇒ R (L Y)
    -- TX ⇒ TY
    ; _≈_ = C._≈_
    ; id = C.id
    ; _∘_ = λ {X} {Y} {Z} f g → (R.F₁ (ε.η (L.F₀ Z)) C.∘ R.F₁ (L.F₁ f)) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (R.F₁ (L.F₁ g)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ X))
    -- (R (ε (L Z)) ∘ R (L f)) ∘ (R (ε (L (R (L Y)))) ∘ R (L (R (L g)))) ∘ η (R (L (R (L X)))) ∘ η (R (L X))
    -- RεLZ ∘ RLf ∘ RεLRLY ∘ RLRLg ∘ ηRLRLX ∘ ηRLX
    -- μZ ∘ Tf ∘ (μTY ∘ TTg) ∘ ηTTX ∘ ηTX
    -- μZ ∘ T(f ∘ g) ∘ (μ TX ∘ ηT TX) ∘ ηTX
    -- μZ ∘ (T(f ∘ g) ∘ ηTX)
    -- (μ Z ∘ ηT Z) ∘ (f ∘ g)
    -- f ∘ g
    ; assoc = {! !}
    ; sym-assoc = {! !}
    ; identityˡ = {! !}
    ; identityʳ = {! !}
    ; identity² = {! !}
    ; equiv = C.equiv
    ; ∘-resp-≈ = {! !}
    }
  _ = refl

  _ : Cofree (kadjoint⇒comonad (L⊣R)) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ {X} {Y} (f : X C.⇒ R.F₀ (L.F₀ Y)) → (R.F₁ (ε.η (L.F₀ Y)) C.∘ R.F₁ (L.F₁ f)) C.∘ C.id }
    -- (R (ε (L Y)) ∘ R (L f)) ∘ 1
    -- RεLY ∘ RLf
    -- μY ∘ Tf  where  f : X → TY
  _ = refl

  _ : Coforgetful (kadjoint⇒comonad (L⊣R)) ≡ record
    { F₀ = λ X → R.F₀ (L.F₀ X)
    -- TX
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (R.F₁ (L.F₁ f)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ X)) }
    -- (R (ε (L (R (L Y)))) ∘ R (L (R (L f)))) ∘ η (R (L (R (L X)))) ∘ η (R (L X))
    -- RεLRLY ∘ RLRLf ∘ ηRLRLX ∘ ηRLX
    -- (μTY ∘ TTf) ∘ ηTTX ∘ ηTX
    -- Tf ∘ (μ TX ∘ ηT TX) ∘ ηTX
    -- (Tf ∘ ηTX)
    -- ηTY ∘ f  where  f : TX → TY
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

