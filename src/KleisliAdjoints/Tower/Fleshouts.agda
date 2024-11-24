{-# OPTIONS --without-K --allow-unsolved-metas #-}
module KleisliAdjoints.Tower.Fleshouts where

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
open import KleisliAdjoints.Tower.L1.Bootstrap using (kOperationalise; kContextualise; kKleisliAdjoints)
open import KleisliAdjoints.Tower.L2.Bootstrap using (kkOperationalise; kkContextualise; kkKleisliAdjoints)

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
    module S = Comonad (adjoint⇒comonad L⊣R)
    module T = Monad (adjoint⇒monad L⊣R)

    Op1 = Operationalise L⊣R
    Co1 = Contextualise L⊣R
    KA1 = KleisliAdjoints L⊣R

    Op2 = kOperationalise L⊣R
    Co2 = kContextualise L⊣R
    KA2 = kKleisliAdjoints L⊣R

    Op3 = kkOperationalise L⊣R
    Co3 = kkContextualise L⊣R
    KA3 = kkKleisliAdjoints L⊣R

    -- Op4 = kkkOperationalise L⊣R
    -- Co4 = kkkContextualise L⊣R
    -- KA4 = kkkKleisliAdjoints L⊣R

  -- Ok, overall doing the following is much simpler: almost instantaneous and much simpler terms.

  _ : Co1 ≡ let open D; open T renaming (F to T); open S using (ε) in record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : X C.⇒ T.F₀ Y) → ε.η (L.F₀ Y) ∘ L.F₁ f ∘ ε.η (L.F₀ X) }
  _ = refl

  _ : Co3 ≡ let open D; open T renaming (F to T); open S using (ε) in record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : T.F₀ X C.⇒ T.F₀ (T.F₀ Y)) → ε.η (L.F₀ (T.F₀ Y)) ∘ L.F₁ f ∘ ε.η (L.F₀ (T.F₀ X)) }
  _ = refl

  _ : Op1 ≡ let open C; open S renaming (F to S); open T using (η) in record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ X D.⇒ Y) → η.η (R.F₀ Y) ∘ R.F₁ f ∘ η.η (R.F₀ X) }
  _ = refl

  _ : Op3 ≡ let open C; open S renaming (F to S); open T using (η) in record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ (S.F₀ X) D.⇒ S.F₀ Y) → η.η (R.F₀ (S.F₀ Y)) ∘ R.F₁ f ∘ η.η (R.F₀ (S.F₀ X)) }
  _ = refl

  _ : KA1 ≡ record
    { unit = record { η = λ X → D.id }
    ; counit = record { η = λ X → C.id } }
  _ = refl

  _ : KA3 ≡ record
    { unit = record { η = λ X → D.id }
    ; counit = record { η = λ X → C.id } }
  _ = refl

  --

  _ : Co2 ≡ let open C; open S renaming (F to S) in record
    { F₀ = R.F₀
    ; F₁ = λ {X} {Y} (f : S.F₀ X D.⇒ S.F₀ Y) → R.F₁ (ε.η (S.F₀ Y)) ∘ R.F₁ (S.F₁ f) ∘ R.F₁ (δ.η X) }
  _ = refl

  -- _ : Co4 ≡ let open C; open S renaming (F to S) in record
  --   { F₀ = R.F₀
  --   ; F₁ = ? }
  -- _ = refl

  _ : Op2 ≡ let open D; open T renaming (F to T) in record
    { F₀ = L.F₀
    ; F₁ = λ {X} {Y} (f : T.F₀ X C.⇒ T.F₀ Y) → L.F₁ (μ.η Y) ∘ L.F₁ (T.F₁ f) ∘ L.F₁ (η.η (T.F₀ X)) }
  _ = refl

  -- _ : Op4 ≡ let open D; open T renaming (F to T) in record
  --   { F₀ = L.F₀
  --   ; F₁ = ? }
  -- _ = refl

  _ : KA2 ≡ let open T using (η) renaming (F to T); open S using (ε) renaming (F to S) in record
    { unit = record { η = λ X → η.η (T.F₀ X) }
    ; counit = record { η = λ X → ε.η (S.F₀ X) } }
  _ = refl

  -- _ : KA4 ≡ let open T using (η) renaming (F to T); open S using (ε) renaming (F to S) in record
  --   { unit = record { η = ? }
  --   ; counit = record { η = ? } }
  -- _ = refl

