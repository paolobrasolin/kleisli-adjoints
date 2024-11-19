{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.Fleshouts where

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
    module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    O⊣C = KleisliAdjoints L⊣R

  _ : adjoint⇒monad (O⊣C) ≡ record
    { F = record
      { F₀ = λ x → L.F₀ (R.F₀ x)
      ; F₁ = λ x → ϵ.η (L.F₀ (R.F₀ _)) D.∘ L.F₁ (η.η (R.F₀ _) C.∘ R.F₁ x C.∘ η.η (R.F₀ _)) D.∘ ϵ.η (L.F₀ (R.F₀ _))
      -- ϵ (L (R _)) ∘ L (η (R _) ∘ R x ∘ η (R _)) ∘ ϵ (L (R _))
      -- ϵLR_ ∘ LηR_ ∘ LRx ∘ LηR_ ∘ ϵLR_
      -- (ϵL R_ ∘ Lη R_) ∘ LRx ∘ LηR_ ∘ ϵLR_
      -- LRx ∘ LηR_ ∘ ϵLR_
      -- Sx ∘ δ_ ∘ ϵS_
      ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
    ; η = record
      { η = λ X → D.id
      ; commute = {! !} ; sym-commute = {! !} }
    ; μ = record
      { η = λ X → ϵ.η (L.F₀ (R.F₀ X)) D.∘ L.F₁ C.id D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ X))))
      -- ϵ (L (R X)) ∘ L 1 ∘ ϵ (L (R (L (R X))))
      -- ϵLRX ∘ ϵLRLRX
      -- ϵSX ∘ ϵSSX
      ; commute = {! !} ; sym-commute = {! !} }
    ; assoc = {! !} ; sym-assoc = {! !} ; identityˡ = {! !} ; identityʳ = {! !} }
  _ = refl

  _ : adjoint⇒comonad (O⊣C) ≡ record
    { F = record
      { F₀ = λ x → R.F₀ (L.F₀ x)
      ; F₁ = λ x → η.η (R.F₀ (L.F₀ _)) C.∘ R.F₁ (ϵ.η (L.F₀ _) D.∘ L.F₁ x D.∘ ϵ.η (L.F₀ _)) C.∘ η.η (R.F₀ (L.F₀ _))
      -- η (R (L _)) ∘ R (ϵ (L _) ∘ L x ∘ ϵ (L _)) ∘ η (R (L _))
      -- ηRL_ ∘ RϵL_ ∘ RLx ∘ RϵL_ ∘ ηRL_
      -- ηRL_ ∘ RϵL_ ∘ RLx ∘ (Rϵ L_ ∘ ηR L_)
      -- ηRL_ ∘ RϵL_ ∘ RLx
      -- ηT_ ∘ μ_ ∘ Tx
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
    module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    O⊣C = KleisliAdjoints L⊣R

  _ : Contextualise O⊣C ≡ record
    { F₀ = R.F₀
    ; F₁ = λ f → (R.F₁ (ϵ.η (L.F₀ (R.F₀ _))) C.∘ R.F₁ (L.F₁ C.id)) C.∘ (R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ _))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ _))) C.∘ R.F₁ f C.∘ η.η (R.F₀ _)))) C.∘ C.id
    -- (R (ϵ (L (R _))) ∘ R (L 1)) ∘ (R (ϵ (L (R (L (R _))))) ∘ R (L (η (R (L (R _))) ∘ R f ∘ η (R _)))) ∘ 1
    -- RϵLR_ ∘ RϵLRLR_ ∘ RLηRLR_ ∘ RLRf ∘ RLηR_
    -- RϵLR_ ∘ (R ϵL RLR_ ∘ R Lη RLR_) ∘ RLRf ∘ RLηR_
    -- RϵLR_ ∘ RLRf ∘ RLηR_
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : Operationalise O⊣C ≡ record
    { F₀ = L.F₀
    ; F₁ = λ f → D.id D.∘ L.F₁ (R.F₁ ((ϵ.η (L.F₀ _) D.∘ L.F₁ f D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ _)))) D.∘ L.F₁ (R.F₁ D.id) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ _))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ _)))
    -- 1 ∘ L (R ((ϵ (L _) ∘ L f ∘ ϵ (L (R (L _)))) ∘ L (R 1) ∘ L (η (R (L _))))) ∘ L (η (R (L _)))
    -- LRϵL_ ∘ LRLf ∘ LRϵLRL_ ∘ LRLηRL_ ∘ LηRL_
    -- LRϵL_ ∘ LRLf ∘ (LR ϵL RL_ ∘ LR Lη RL_) ∘ LηRL_
    -- LRϵL_ ∘ LRLf ∘ LηRL_
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : KleisliAdjoints O⊣C ≡ record
    { unit = record
      { η = λ X → η.η (R.F₀ (L.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; counit = record
      { η = λ X → ϵ.η (L.F₀ (R.F₀ X))
      ; commute = {! !} ; sym-commute = {! !} }
    ; zig = {! !}
    ; zag = {! !}
    }
  _ = refl

