module KleisliAdjoints.Fleshout.CoKleisli where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Construction.CoKleisli using (Forgetful⊣Cofree)
open import Categories.Adjoint.Properties using (adjoint⇒comonad)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open import KleisliAdjoints using (Contextualise; Operationalise)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where
  F⊣G = Forgetful⊣Cofree (adjoint⇒comonad Adj)

  open module D = Category D
  module G = Functor G
  module F = Functor F
  module H = NaturalTransformation (Adjoint.unit Adj)
  open H renaming (η to η)
  module E = NaturalTransformation (Adjoint.counit Adj)
  open E renaming (η to ϵ)

  _ : Functor.F₀ (Contextualise F⊣G) ≡ λ x → F.F₀ (G.F₀ x)
  _ = refl
  _ : Functor.F₁ (Contextualise F⊣G) ≡ λ f → ϵ (F.F₀ (G.F₀ _)) ∘ (F.F₁ (G.F₁ f) ∘ F.F₁ (η (G.F₀ _))) ∘ ϵ (F.F₀ (G.F₀ _))
  _ = refl

  _ : Functor.F₀ (Operationalise F⊣G) ≡ λ X → X
  _ = refl
  _ : Functor.F₁ (Operationalise F⊣G) ≡ λ f → F.F₁ (G.F₁ id) ∘ F.F₁ (G.F₁ ((f ∘ ϵ (F.F₀ (G.F₀ _))) ∘ F.F₁ (G.F₁ (F.F₁ (G.F₁ id))) ∘ F.F₁ (η (G.F₀ _)))) ∘ F.F₁ (η (G.F₀ _))
  _ = refl

