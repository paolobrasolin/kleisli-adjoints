module KleisliAdjoints.Fleshout.Kleisli where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful)
open import Categories.Adjoint.Properties using (adjoint⇒monad)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where
  F⊣G = Free⊣Forgetful (adjoint⇒monad Adj)

  open module C = Category C
  module G = Functor G
  module F = Functor F
  module H = NaturalTransformation (Adjoint.unit Adj)
  open H renaming (η to η)
  module E = NaturalTransformation (Adjoint.counit Adj)
  open E renaming (η to ϵ)

  _ : Functor.F₀ (Contextualise F⊣G) ≡ λ X → X
  _ = refl
  _ : Functor.F₁ (Contextualise F⊣G) ≡ λ f → (G.F₁ (ϵ (F.F₀ _)) ∘ G.F₁ (F.F₁ (G.F₁ (F.F₁ C.id)))) ∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _)))) ∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ _)) ∘ f))) ∘ G.F₁ (F.F₁ C.id)
  -- (GϵF_ ∘ GFGF1) ∘ (GϵFGF_ ∘ GF(ηGF_ ∘ f)) ∘ GF1
  -- GϵF_ ∘ (GϵFGF_ ∘ GF(ηGF_ ∘ f))
  -- μ_ ∘ μT_ ∘ T(ηT_ ∘ f)
  -- μ_ ∘ Tμ_ ∘ T(ηT_ ∘ f)
  -- μ_ ∘ T(μ_ ∘ ηT_ ∘ f)
  -- μ_ ∘ T(1 ∘ f)
  -- μ_ ∘ Tf
  _ = refl

  _ : Functor.F₀ (Operationalise F⊣G) ≡ λ x → G.F₀ (F.F₀ x)
  _ = refl
  _ : Functor.F₁ (Operationalise F⊣G) ≡ λ f → η (G.F₀ (F.F₀ _)) ∘ (G.F₁ (ϵ (F.F₀ _)) ∘ G.F₁ (F.F₁ f)) ∘ η (G.F₀ (F.F₀ _))
  -- ηGF_ ∘ GϵF_ ∘ GFf ∘ ηGF_
  -- ηT_ ∘ μ_ ∘ Tf ∘ ηT_
  -- ηT_ ∘ μ_ ∘ Tf ∘ ηT_
  _ = refl

