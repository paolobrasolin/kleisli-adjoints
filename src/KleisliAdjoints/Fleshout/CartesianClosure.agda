module KleisliAdjoints.Fleshout.CartesianClosure where

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

-- adjunction: cartesian closed, monad: state, comonad: store
module _ {S : Set o} where
  _×S : Functor (Sets o) (Sets o)
  _×S = record
    { F₀ = λ { X → X × S }
    ; F₁ = map₁
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  _^S : Functor (Sets o) (Sets o)
  _^S = record
    { F₀ = λ { X → S → X }
    ; F₁ = λ { f g s → f (g s) }
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  ×S⊣^S : _×S ⊣ _^S
  ×S⊣^S = record
    { unit = record
      { η = λ { X x s → x , s }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; counit = record
      { η = λ { X (f , s) → f s }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; zig = {! !}
    ; zag = {! !}
    }

  _ : Functor.F₀ (Contextualise ×S⊣^S) ≡ λ { X → Σ X (λ _ → S) }
  _ = refl

  _ : Functor.F₁ (Contextualise ×S⊣^S) ≡ λ { f (g , s) → f (proj₁ (g s)) (proj₂ (g s)) }
  _ = refl

  _ : Functor.F₀ (Operationalise ×S⊣^S) ≡ λ { X → S → X }
  _ = refl

  _ : Functor.F₁ (Operationalise ×S⊣^S) ≡ λ { f g s → (λ { x → f (g , x) }) , s }
  _ = refl

