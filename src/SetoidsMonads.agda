module SetoidsMonads where

open import Level
open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)

-- open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
-- open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful)

open import Data.Product using (_×_; _,_; map₁; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.PointedSets using (Underlying; PointedSets)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open import KleisliAdjoints using (Contextualise; Operationalise)

module Maybe {o : Level} where
  _+1 : Functor (Sets o) (PointedSets o)
  _+1 = record
    { F₀ = λ { x → (x ⊎ ⊤) , inj₂ tt }
    ; F₁ = λ { f → (λ { (inj₁ x) → inj₁ (f x)
                      ; (inj₂ tt) → inj₂ tt }) , refl }
    ; identity = {! !}
    ; homomorphism = {! !}
    ; F-resp-≈ = {! !}
    }

  +1⊣Underlying : _+1 ⊣ Underlying
  +1⊣Underlying = record
    { unit = record
      { η = λ { X x → inj₁ x }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; counit = record
      { η = λ { (X , x) → (λ { (inj₁ a) → a
                             ; (inj₂ tt) → x }) , refl }
      ; commute = {! !}
      ; sym-commute = {! !}
      }
    ; zig = {! !}
    ; zag = {! !}
    }

  _ : Functor.F₀ (Contextualise +1⊣Underlying) ≡ λ { X → (X ⊎ ⊤) , inj₂ tt }
  _ = refl

  _ : Functor.F₁ (Contextualise +1⊣Underlying) ≡ λ { f → (λ { (inj₁ (inj₁ x)) → f x
                                                            ; (inj₁ (inj₂ tt)) → inj₂ tt
                                                            ; (inj₂ tt) → inj₂ tt }) , refl }
  _ = ≡.cong (λ { x f → f , refl }) refl

  _ : Functor.F₀ (Operationalise +1⊣Underlying) ≡ λ { (X , x) → X }
  _ = refl

  _ : Functor.F₁ (Operationalise +1⊣Underlying) ≡ λ { (f , _) x → inj₁ (f (inj₁ x)) }
  _ = refl

module State {o : Level} {S : Set o} where
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

