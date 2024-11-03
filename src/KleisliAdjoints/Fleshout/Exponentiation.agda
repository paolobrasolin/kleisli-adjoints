module KleisliAdjoints.Fleshout.Exponentiation where

open import Level
open import Agda.Builtin.Equality using (_≡_; refl)

open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)

open import KleisliAdjoints using (Contextualise; Operationalise)

private
  variable
    o : Level

-- adjunction: exponentiation, monad: continuation, comonad: ?
module _ {S : Set o} where
  S^_ : Functor (Category.op (Sets o)) (Sets o)
  S^_ = record
    { F₀ = λ { X → X → S }
    ; F₁ = λ { f g x → g (f x) }
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  S^_⊣S^_ : (Functor.op S^_) ⊣ S^_
  S^_⊣S^_ = record
    { unit = record
      { η = λ { _ x f → f x }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; counit = record
      { η = λ { _ x f → f x }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; zig = {! !}
    ; zag = {! !}
    }

  _ : Functor.F₀ (Contextualise S^_⊣S^_) ≡ λ X → X → S
  _ = refl

  _ : Functor.F₁ (Contextualise S^_⊣S^_) ≡ λ { f g h → h (λ x → f x g) }
  _ = refl

  _ : Functor.F₀ (Operationalise S^_⊣S^_) ≡ λ X → X → S
  _ = refl

  _ : Functor.F₁ (Operationalise S^_⊣S^_) ≡ λ { f g h → h (λ x → f x g) }
  _ = refl


