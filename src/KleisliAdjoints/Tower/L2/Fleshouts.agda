{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.L2.Fleshouts where

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

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)
open import KleisliAdjoints.Tower.L1.Bootstrap using (kadjoint⇒monad; kadjoint⇒comonad; kOperationalise; kContextualise; kKleisliAdjoints)
open import KleisliAdjoints.Tower.L2.Bootstrap using (kkadjoint⇒monad; kkadjoint⇒comonad)

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

  _ : adjoint⇒monad (kKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → R.F₀ (L.F₀ X) -- TX
      ; F₁ = λ f → R.F₁ (L.F₁ f) } -- Tf
    ; η = record
      { η = λ X → η.η (R.F₀ (L.F₀ X)) } -- ηTX
    ; μ = record
      { η = λ X → R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ X)))) } -- μTX
    }
  _ = refl

  _ : adjoint⇒comonad (kKleisliAdjoints L⊣R) ≡ record
    { F = record
      { F₀ = λ X → L.F₀ (R.F₀ X) -- SX
      ; F₁ = λ f → L.F₁ (R.F₁ f) } -- Sf
    ; ε = record
      { η = λ X → ε.η (L.F₀ (R.F₀ X)) } -- εSX
    ; δ = record
      { η = λ X → L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))) } } -- δSX
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

  _ : Kleisli (kkadjoint⇒monad (L⊣R)) ≡ record
    { Obj = ? -- D.Obj
    ; _⇒_ = λ A B → R.F₀ (L.F₀ A) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ B))) -- λ X Y → L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)
    -- L (R X) ⇒ L (R Y)
    -- SX ⇒ SY
    ; _≈_ = ? -- D._≈_
    ; id = ? -- D.id
    ; _∘_ = ? -- λ {X} {Y} {Z} f g → ((ε.η (L.F₀ (R.F₀ Z)) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Z))))) D.∘ L.F₁ (R.F₁ (L.F₁ (R.F₁ f))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ Y))))) D.∘ L.F₁ (R.F₁ g) D.∘ L.F₁ (η.η (R.F₀ X))
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
    ; equiv = ? -- D.equiv
    ; ∘-resp-≈ = {! !}
    }
  _ = refl

  _ : Free (kkadjoint⇒monad (L⊣R)) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)) → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ Y))))) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (R.F₁ (L.F₁ f)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ X)) }
    -- (R (ε (L (R (L Y)))) ∘ R (L (η (R (L Y))))) ∘ (R (ε (L (R (L Y)))) ∘ R (L (R (L f)))) ∘ η (R (L (R (L X)))) ∘ η (R (L X))
    -- RεLRLY ∘ RLηRLY ∘ RεLRLY ∘ RLRLf ∘ ηRLRLX ∘ ηRLX
    -- (μ TY ∘ Tη TY) ∘ μTY ∘ (TTf ∘ ηTTX) ∘ ηTX
    -- (μ TY ∘ ηT TY) ∘ (Tf ∘ ηTX)
    -- ηTY ∘ f  where  f : TX → TY
  _ = refl

  _ : Forgetful (kkadjoint⇒monad (L⊣R)) ≡ record
    { F₀ = λ X → R.F₀ (L.F₀ X)
    -- TX
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) → (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y))))))) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))))))) C.∘ R.F₁ (L.F₁ (R.F₁ (L.F₁ (R.F₁ (L.F₁ f)))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) }
    -- (R (ε (L (R (L Y)))) ∘ R (L (R (ε (L (R (L Y))))))) ∘ (R (ε (L (R (L (R (L (R (L Y)))))))) ∘ R (L (R (L (R (L f)))))) ∘ η (R (L (R (L (R (L X)))))) ∘ η (R (L (R (L X))))
    -- RεLRLY ∘ RLRεLRLY ∘ RεLRLRLRLY ∘ RLRLRLf ∘ ηRLRLRLX ∘ ηRLRLX
    -- μTY ∘ TμTY ∘ μTTTY ∘ (TTTf ∘ ηTTTX) ∘ ηTTX
    -- (μTY ∘ TμTY) ∘ (μ TTTY ∘ ηT TTTY) ∘ (TTf ∘ ηTTX)
    -- μTY ∘ μTTY ∘ (μ TTTY ∘ ηT TTTY) ∘ (TTf ∘ ηTTX)
    -- μTY ∘ (μ TTY ∘ ηT TTY) ∘ Tf
    -- (μTY ∘ Tf)
    -- f ∘ μX  where  f : TX → TTY
  _ = refl

  _ : CoKleisli (kkadjoint⇒comonad (L⊣R)) ≡ record
    { Obj = ? -- C.Obj
    ; _⇒_ = ? -- λ X Y → R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ Y)
    -- R (L X) ⇒ R (L Y)
    -- TX ⇒ TY
    ; _≈_ = ? -- C._≈_
    ; id = ? -- C.id
    ; _∘_ = ? -- λ {X} {Y} {Z} f g → (R.F₁ (ε.η (L.F₀ Z)) C.∘ R.F₁ (L.F₁ f)) C.∘ (R.F₁ (ε.η (L.F₀ (R.F₀ (L.F₀ Y)))) C.∘ R.F₁ (L.F₁ (R.F₁ (L.F₁ g)))) C.∘ η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))) C.∘ η.η (R.F₀ (L.F₀ X))
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
    ; equiv = ? -- C.equiv
    ; ∘-resp-≈ = {! !}
    }
  _ = refl

  _ : Cofree (kkadjoint⇒comonad (L⊣R)) ≡ record
    { F₀ = λ X → X
    -- X
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ X) D.⇒ L.F₀ (R.F₀ Y)) → ((ε.η (L.F₀ (R.F₀ Y)) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))) D.∘ L.F₁ (R.F₁ (L.F₁ (R.F₁ f))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X))))) D.∘ L.F₁ (R.F₁ (ε.η (L.F₀ (R.F₀ X)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))) }
    -- ((ε (L (R Y)) ∘ ε (L (R (L (R Y))))) ∘ L (R (L (R f))) ∘ L (η (R (L (R X))))) ∘ L (R (ε (L (R X)))) ∘ L (η (R (L (R X))))
    -- εLRY ∘ εLRLRY ∘ LRLRf ∘ LηRLRX ∘ LRεLRX ∘ LηRLRX
    -- εSY ∘ εSSY ∘ (SSf ∘ δSX) ∘ (Sε SX ∘ δ SX)
    -- εSY ∘ (εS SY ∘ δ SY) ∘ Sf
    -- (εSY ∘ Sf)
    -- f ∘ εSX  where  f : SX → SY
  _ = refl

  _ : Coforgetful (kkadjoint⇒comonad (L⊣R)) ≡ record
    { F₀ = λ x → L.F₀ (R.F₀ x)
    -- SX
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ (L.F₀ (R.F₀ X))) D.⇒ L.F₀ (R.F₀ Y)) → ((ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y)))) D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ Y))))))) D.∘ L.F₁ (R.F₁ (L.F₁ (R.F₁ (L.F₁ (R.F₁ f))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))))))) D.∘ L.F₁ (R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ X)))) }
    -- ((ε (L (R (L (R Y)))) ∘ ε (L (R (L (R (L (R Y))))))) ∘ L (R (L (R (L (R f))))) ∘ L (η (R (L (R (L (R (L (R X))))))))) ∘ L (R (L (η (R (L (R X)))))) ∘ L (η (R (L (R X))))
    -- εLRLRY ∘ εLRLRLRY ∘ LRLRLRf ∘ LηRLRLRLRX ∘ LRLηRLRX ∘ LηRLRX
    -- εSSY ∘ εSSSY ∘ SSSf ∘ δSSSX ∘ SδSX ∘ δSX
    -- εSSY ∘ (εSSSY ∘ SSSf) ∘ δSSSX ∘ SδSX ∘ δSX
    -- (εSSY ∘ SSf) ∘ (εS SSSY ∘ δ SSSX) ∘ (Sδ SX ∘ δ SX)
    -- Sf ∘ (εS SSX ∘ δ SSX) ∘ δSX
    -- (Sf ∘ δSX)
    -- δSY ∘ f  where  f : SSX → SY
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
    ; F₁ = λ {X} {Y} (f : R.F₀ (L.F₀ X) C.⇒ R.F₀ (L.F₀ (R.F₀ (L.F₀ Y)))) → ε.η (L.F₀ (R.F₀ (L.F₀ Y))) D.∘ L.F₁ f D.∘ ε.η (L.F₀ (R.F₀ (L.F₀ X))) }
    -- ε (L (R (L Y))) ∘ L f ∘ ε (L (R (L X)))
    -- εLRLY ∘ Lf ∘ εLRLX
    -- ϵLTY ∘ Lf ∘ ϵLTX where f : TX → TTY
  _ = refl

  _ : kOperationalise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : L.F₀ (R.F₀ (L.F₀ (R.F₀ X))) D.⇒ L.F₀ (R.F₀ Y)) → η.η (R.F₀ (L.F₀ (R.F₀ Y))) C.∘ R.F₁ f C.∘ η.η (R.F₀ (L.F₀ (R.F₀ X))) }
    -- η (R (L (R Y))) ∘ R f ∘ η (R (L (R X)))
    -- ηRLRY ∘ Rf ∘ ηRLRX
    -- ηRSY ∘ Rf ∘ ηRSX where f : SSX → SY
  _ = refl

  _ : kKleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → D.id }
    ; counit = record
      { η = λ X → C.id }
    }
  _ = refl

