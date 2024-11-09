{-# OPTIONS --without-K --safe #-}
module KleisliAdjoints.Properties where

open import Level
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful)
open import Categories.Adjoint.Properties using (adjoint⇒monad)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)


open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
import Categories.Morphism.Reasoning as MR

open import Categories.NaturalTransformation.NaturalIsomorphism -- using (niHelper; NaturalIsomorphism)
open import Categories.Category.Equivalence

domOf : {o ℓ e o′ ℓ′ e′ : Level} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (Functor C D) → Category o ℓ e
domOf {C = C} = λ { _ → C }

codOf : {o ℓ e o′ ℓ′ e′ : Level} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (Functor C D) → Category o′ ℓ′ e′
codOf {D = D} = λ { _ → D }

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module InvolutionOnSelf {F : Functor C D} {G : Functor D C} (KA0 : F ⊣ G) where
  KA1 = KleisliAdjoints KA0
  KA2 = KleisliAdjoints KA1
  KA3 = KleisliAdjoints KA2

  module C = Category C
  module D = Category D
  module G = Functor G
  module F = Functor F
  module H = NaturalTransformation (Adjoint.unit KA0)
  open H renaming (η to η)
  module E = NaturalTransformation (Adjoint.counit KA0)
  open E renaming (η to ϵ)

  DomEq : StrongEquivalence (domOf (Contextualise KA0)) (domOf (Contextualise KA2))
  DomEq = ?

  CodEq : StrongEquivalence (codOf (Contextualise KA0)) (codOf (Contextualise KA2))
  CodEq = ?

  open module CodEq = StrongEquivalence CodEq
  open module DomEq = StrongEquivalence DomEq

  _ : NaturalIsomorphism (Contextualise KA0 ∘F DomEq.G) (CodEq.G ∘F Contextualise KA2)
  _ = ?

  _ : NaturalIsomorphism (CodEq.F ∘F Contextualise KA0) (Contextualise KA2 ∘F DomEq.F)
  _ = ?

