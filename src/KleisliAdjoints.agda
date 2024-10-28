open import Categories.Category

module KleisliAdjoints { o l e o' l' e' } { C : Category o l e } { D : Category o' l' e' } where

open import Categories.Adjoint
open import Categories.Functor
open import Categories.Monad
open import Categories.Comonad

-- open import Categories.Adjoint.Construction.Kleisli
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Construction.CoKleisli

open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)

open import Categories.Morphism.Reasoning as MR

pollo : { F : Functor C D } { G : Functor D C } → ( Adj : F ⊣ G )
  → Functor (Kleisli (adjoint⇒monad Adj)) (CoKleisli (adjoint⇒comonad Adj))
pollo {F} {G} Adj = record
  { F₀ = F.F₀
  ; F₁ = λ { f → Adj.counit.η (F.F₀ _) D.∘ (F.F₁ f) D.∘ Adj.counit.η (F.F₀ _) }
  ; identity = λ { {A} → begin
      _ ≈⟨ MR.cancelˡ D Adj.zig ⟩
      _ ∎
    }
  ; homomorphism = {! !}
  ; F-resp-≈ = {! !}
  } where module F = Functor F
          module D = Category D
          module Adj = Adjoint Adj
          open D.HomReasoning
          open MR D

gallo : { F : Functor C D } { G : Functor D C } → ( Adj : F ⊣ G )
  → Functor (CoKleisli (adjoint⇒comonad Adj)) (Kleisli (adjoint⇒monad Adj))
gallo {F} {G} Adj = ?

gallo⊣pollo : { F : Functor C D } { G : Functor D C } → (Adj : F ⊣ G) → ( (gallo Adj) ⊣ (pollo Adj) )
gallo⊣pollo = {! !}

