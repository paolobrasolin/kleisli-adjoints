import Level
open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)

open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful)

module KleisliExample  {o l e o' l' e'} {C : Category o l e} {D : Category o' l' e'} {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where

open import KleisliAdjoints (Free⊣Forgetful (adjoint⇒monad Adj))

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.NaturalTransformation.Core
open import Categories.Monad
open import Categories.Category.Construction.Kleisli

_ : let
      open module C = Category C
      module G = Functor G
      module F = Functor F
      module H = NaturalTransformation (Adjoint.unit Adj)
      open H renaming (η to η)
      module E = NaturalTransformation (Adjoint.counit Adj)
      open E renaming (η to ϵ)
    in pollo ≡ record
  { F₀ = λ { x → x }
  ; F₁ = λ { f → (G.F₁ (ϵ (F.F₀ _)) ∘ G.F₁ (F.F₁ (G.F₁ (F.F₁ C.id)))) ∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _)))) ∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ _)) ∘ f))) ∘ G.F₁ (F.F₁ C.id) }
  -- (GϵF_ ∘ GFGF1) ∘ (GϵFGF_ ∘ GF(ηGF_ ∘ f)) ∘ GF1
  -- GϵF_ ∘ (GϵFGF_ ∘ GF(ηGF_ ∘ f))
  -- μ_ ∘ μT_ ∘ T(ηT_ ∘ f)
  -- μ_ ∘ Tμ_ ∘ T(ηT_ ∘ f)
  -- μ_ ∘ T(μ_ ∘ ηT_ ∘ f)
  -- μ_ ∘ T(1 ∘ f)
  -- μ_ ∘ Tf
  ; identity = {! !}
  ; homomorphism = {! !}
  ; F-resp-≈ = {! !}
  }
_ = refl

module _ where
  open module C = Category C
  module G = Functor G
  module F = Functor F
  module H = NaturalTransformation (Adjoint.unit Adj)
  open H renaming (η to η)
  module E = NaturalTransformation (Adjoint.counit Adj)
  open E renaming (η to ϵ)
  _ : Functor.F₀ gallo ≡ λ x → G.F₀ (F.F₀ x)
  _ = refl
  _ : Functor.F₁ gallo ≡ λ f → η (G.F₀ (F.F₀ _)) ∘ (G.F₁ (ϵ (F.F₀ _)) ∘ G.F₁ (F.F₁ f)) ∘ η (G.F₀ (F.F₀ _))
  -- ηGF_ ∘ GϵF_ ∘ GFf ∘ ηGF_
  -- ηT_ ∘ μ_ ∘ Tf ∘ ηT_
  -- ηT_ ∘ μ_ ∘ Tf ∘ ηT_
  _ = refl


