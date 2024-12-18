module KleisliAdjoints.Fleshout.FlubbaWubba where

open import Level
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; map₁; map₂; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)

open import KleisliAdjoints using (Contextualise; Operationalise)

private
  variable
    o : Level

-- adjunction: flubba wubba, monad: ? comonad: product
module _ {S : Set o} where
  open import Categories.Category.Slice (Sets o)
  open import Function using (_∘_)

  dom : Functor (Slice S) (Sets o)
  dom = record
    { F₀ = SliceObj.Y
    ; F₁ = Slice⇒.h
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  pie : Functor (Sets o) (Slice S)
  pie = record
    { F₀ = λ { X → sliceobj {Y = X × S} proj₂ }
    ; F₁ = λ { f → slicearr {h = map₁ f} refl }
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  dom⊣pie : dom ⊣ pie
  dom⊣pie = record
    { unit = record
      { η = λ { f → slicearr {h = map₂ (SliceObj.arr f) ∘ λ { x → x , x }} refl }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; counit = record
      { η = λ { X (x , s) → x }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; zig = {! !}
    ; zag = {! !}
    }

  _ : Functor.F₀ (Contextualise dom⊣pie) ≡ SliceObj.Y
  _ = refl

  _ : Functor.F₁ (Contextualise dom⊣pie) ≡ λ f x → proj₁ (Slice⇒.h f (proj₁ x))
  _ = refl

  _ : Functor.F₀ (Operationalise dom⊣pie) ≡ λ X → sliceobj (λ r → proj₂ r)
  _ = refl

  _ : Functor.F₁ (Operationalise dom⊣pie) ≡ λ f → slicearr refl
  _ = refl

  open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
  open import Categories.Monad
  open import Categories.Comonad
  dompie = adjoint⇒comonad dom⊣pie
  piedom = adjoint⇒monad dom⊣pie
  _ : Functor.F₀ (Comonad.F dompie) ≡ λ x → Σ x (λ x₁ → S)
  _ = refl
  _ : Functor.F₁ (Comonad.F dompie) ≡ λ x → Data.Product.map x (λ x₁ → x₁)
  _ = refl
  _ : Functor.F₀ (Monad.F piedom) ≡ λ x → sliceobj (λ r → proj₂ r)
  _ = refl
  _ : Functor.F₁ (Monad.F piedom) ≡ λ x → slicearr refl
  _ = refl

  open import Categories.Category.Construction.Kleisli using (Kleisli)
  open import Categories.Category.Construction.CoKleisli using (CoKleisli)

  _ : Kleisli piedom ≡ record
    { Obj = SliceObj S
    ; _⇒_ = λ A B → Slice⇒ A (sliceobj (λ r → proj₂ r))
    ; _≈_ = {! !}
    ; id = {! !}
    ; _∘_ = {! !} -- TODO: ?
    ; assoc = {! !}
    ; sym-assoc = {! !}
    ; identityˡ = {! !}
    ; identityʳ = {! !}
    ; identity² = {! !}
    ; equiv = {! !}
    ; ∘-resp-≈ = {! !}
    }
  _ = refl


