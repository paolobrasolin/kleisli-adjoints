module KleisliAdjoints.Fleshout.Self where

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
  KAdj1 = KleisliAdjoints Adj
  KAdj2 = KleisliAdjoints KAdj1

  module C = Category C
  module D = Category D
  module G = Functor G
  module F = Functor F
  module H = NaturalTransformation (Adjoint.unit Adj)
  open H renaming (η to η)
  module E = NaturalTransformation (Adjoint.counit Adj)
  open E renaming (η to ϵ)

  _ : Functor.F₀ (Contextualise KAdj2) ≡ F.F₀
  _ = refl
  _ : Functor.F₁ (Contextualise KAdj2) ≡ λ f → ((ϵ (F.F₀ (G.F₀ (F.F₀ _))) D.∘ F.F₁ C.id D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) D.∘ F.F₁ (G.F₁ (((ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ C.id D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (D.id D.∘ F.F₁ (G.F₁ ((ϵ (F.F₀ (G.F₀ (F.F₀ _))) D.∘ F.F₁ f D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ _)))) D.∘ F.F₁ (G.F₁ D.id) D.∘ F.F₁ (η (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ _)))) C.∘ η (G.F₀ (F.F₀ _))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))
  _ = refl

  _ : Functor.F₀ (Operationalise KAdj2) ≡ G.F₀
  _ = refl
  _ : Functor.F₁ (Operationalise KAdj2) ≡ λ f → (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _)))))) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ _)) D.∘ F.F₁ ((G.F₁ (ϵ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (F.F₁ ((G.F₁ (ϵ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (F.F₁ C.id)) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _))) C.∘ G.F₁ f C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))))) C.∘ C.id))) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ D.id C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ D.id C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))
  _ = refl

