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
  _ : Functor.F₁ (Contextualise KAdj2) ≡ λ { f → ((ϵ (F.F₀ (G.F₀ (F.F₀ _))) D.∘ F.F₁ C.id D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) D.∘ F.F₁ (G.F₁ (((ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ C.id D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (D.id D.∘ F.F₁ (G.F₁ ((ϵ (F.F₀ (G.F₀ (F.F₀ _))) D.∘ F.F₁ f D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ _)))) D.∘ F.F₁ (G.F₁ D.id) D.∘ F.F₁ (η (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ _)))) C.∘ η (G.F₀ (F.F₀ _))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) D.∘ F.F₁ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) }
  -- ϵFGF_ ∘ ϵFGFGF_ ∘ FGϵFGFGF_ ∘ FGFηGFGF_ ∘ FGFGϵFGF_ ∘ FGFηGFGF_ ∘ FGϵFGFGF_ ∘ FηGFGFGF_ ∘ FGϵFGFGF_ ∘ FGϵFGFGFGF_ ∘ FGFGϵFGFGFGF_ ∘ FGFGFηGFGFGF_ ∘ FGFGFGFGϵFGF_ ∘ FGFGFGFGFf ∘ FGFGFGFGϵFGF_ ∘ FGFGFGFGFηGF_ ∘ FGFGFGFηGF_ ∘ FGFGFηGF_ ∘ FGFGϵFGF_ ∘ FGFηGFGF_ ∘ FGFGϵFGF_ ∘ FGFηGFGF_ ∘ FηGFGF_
  -- ϵSF_ ∘ ϵSSF_ ∘ SϵSSF_ ∘ SδSF_ ∘ SSϵSF_ ∘ SδSF_ ∘ SϵSSF_ ∘ δSSF_ ∘ SϵSSF_ ∘ SϵSSSF_ ∘ SSϵSSSF_ ∘ SSδSSF_ ∘ SSSSϵSF_ ∘ SSSSFf ∘ SSSSϵSF_ ∘ SSSSδF_ ∘ SSSδF_ ∘ SSδF_ ∘ SSϵSF_ ∘ SδSF_ ∘ SSϵSF_ ∘ SδSF_ ∘ δSF_ -- FG = S, FηG = δ
  -- ϵSF_ ∘ ϵSSF_ ∘ SSϵSF_ ∘ SδSF_ ∘ SϵSSF_ ∘ δSSF_ ∘ SϵSSF_ ∘ SϵSSSF_ ∘ SSSSϵSF_ ∘ SSSSFf ∘ SSSδF_ ∘ SSδF_ ∘ SSϵSF_ ∘ SδSF_ ∘ SSϵSF_ ∘ SδSF_ ∘ δSF_ -- ?(ϵS? ∘ δ? = 1)
  -- ϵSF_ ∘ ϵSSF_ ∘ SϵSSF_ ∘ SϵSSSF_ ∘ SSSSϵSF_ ∘ SSSSFf ∘ SSSδF_ ∘ SSδF_ ∘ δSF_ -- ?(Sϵ? ∘ δ? = 1)
  -- ϵSF_ ∘ SϵSF_ ∘ SSϵSF_ ∘ SSSϵSF_ ∘ SSSϵSSF_ ∘ SSSSFf ∘ SSSδF_ ∘ SSδF_ ∘ δSF_ -- ϵ? ∘ Sϵ? = ϵ? ∘ ϵS?
  -- ϵSF_ ∘ SϵSF_ ∘ SSϵSF_ ∘ SSSϵSF_ ∘ SSSFf ∘ SSSϵSF_ ∘   SSSδF_ ∘ SSδF_ ∘ δSF_ -- ϵ? ∘ Sϵ? = ϵ? ∘ ϵS?
  -- ϵSF_ ∘ SϵSF_ ∘ SϵSSF_ ∘ SSFf ∘ SSϵ_ ∘ SSSϵSF_ ∘ SSSδF_ ∘ SSδF_ ∘ δSF_ --
  -- ϵSF_ ∘ Ff ∘ ϵSF_
  _ = refl

  _ : Functor.F₁ (Contextualise Adj) ≡ λ f → ϵ (F.F₀ _) D.∘ F.F₁ f D.∘ ϵ (F.F₀ _)
  -- ϵF_ ∘ Ff ∘ ϵF_
  _ = refl

  _ : Functor.F₀ (Operationalise KAdj2) ≡ G.F₀
  _ = refl
  _ : Functor.F₁ (Operationalise KAdj2) ≡ λ f → {! !} -- (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _)))))) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ _)) D.∘ F.F₁ ((G.F₁ (ϵ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (F.F₁ ((G.F₁ (ϵ (F.F₀ (G.F₀ _))) C.∘ G.F₁ (F.F₁ C.id)) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _))) C.∘ G.F₁ f C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))))) C.∘ C.id))) C.∘ (G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))))) C.∘ G.F₁ (F.F₁ (η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ (ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ F.F₁ (η (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ D.id C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))) D.∘ ϵ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _)))))))) C.∘ η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ _))))) C.∘ G.F₁ D.id C.∘ η (G.F₀ (F.F₀ (G.F₀ _)))
  -- GϵFGFG_ ∘ GFηGFG_ ∘ GϵFGFG_ ∘ GFηGFG_ ∘ GFGϵFG_ ∘ GFGFGϵFG_ ∘ GFGFGFGϵFG_ ∘ GFGFGFGϵFGFG_ ∘ GFGFGFGFηGFG_ ∘ GFGFGFGFGf ∘ GFGFGFGFηGFG_ ∘ GFGFGϵFGFGFG_ ∘ GFGFGFηGFGFG_ ∘ GFGFGFGϵFGFG_ ∘ GFGFGFGFηGFG_ ∘ GFGFGFGϵFGFG_ ∘ GFGFGFηGFGFG_ ∘ GFGFηGFGFG_ ∘ GFGFηGFG_ ∘ GFGϵFGFG_ ∘ GFηGFGFG_ ∘ ηGFGFG_ ∘ ηGFG_
  -- μTG_ ∘ TηTG_ ∘ μTG_ ∘ TηTG_ ∘ TμG_ ∘ TTμG_ ∘ TTTμG_ ∘ TTTμTG_ ∘ TTTTηTG_ ∘ TTTTGf ∘ TTTTηTG_ ∘ TTμTTG_ ∘ TTTηTTG_ ∘ TTTμTG_ ∘ TTTTηTG_ ∘ TTTμTG_ ∘ TTTηTTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ TμTG_ ∘ TηTTG_ ∘ ηTTG_ ∘ ηTG_
  -- TμG_ ∘ TTμG_ ∘ TTTμG_ ∘ TTTTGf ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- T(μG_ ∘ TμG_ ∘ TTμG_) ∘ TTTTGf ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- T(μG_ ∘ μTG_ ∘ μTTG_) ∘ TTTTGf ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- TμG_ ∘ TμTG_ ∘ TμTTG_ ∘ TTTTGf ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- TμG_ ∘ TμTG_ ∘ TTμTG_ ∘ TTTTGf ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- TμG_ ∘ TTTGf ∘ TμTTGX ∘ TTμTTGX ∘ TTTTηTG_ ∘ TTηTTG_ ∘ TTηTG_ ∘ ηTTG_ ∘ ηTG_
  -- TGf ∘ ηTTG_ ∘ ηTG_
  _ = refl

