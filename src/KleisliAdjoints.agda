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


pollo : { F : Functor C D } { G : Functor D C } → ( Adj : F ⊣ G )
  → Functor (Kleisli (adjoint⇒monad Adj)) (CoKleisli (adjoint⇒comonad Adj))
pollo = {! !}

gallo : { F : Functor C D } { G : Functor D C } → ( Adj : F ⊣ G )
  → Functor (CoKleisli (adjoint⇒comonad Adj)) (Kleisli (adjoint⇒monad Adj))
gallo = {! !}

gallo⊣pollo : { F : Functor C D } { G : Functor D C } → (Adj : F ⊣ G) → ( (gallo Adj) ⊣ (pollo Adj) )
gallo⊣pollo = {! !}

