{-# OPTIONS --without-K #-}
module KleisliAdjoints.Tower.Sides where

open import Level

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Functor using (Functor; Endofunctor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful; Free; Forgetful)
open import Categories.Adjoint.Construction.CoKleisli using (Forgetful⊣Cofree; Cofree) renaming (Forgetful to Coforgetful)
open import Categories.Monad using (Monad)
open import Categories.Comonad using (Comonad)

import Categories.Morphism.Reasoning as MR

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)

open import KleisliAdjoints.Tower.L1.Bootstrap using (kFree; kForgetful; kCofree; kCoforgetful)
open import KleisliAdjoints.Tower.L2.Bootstrap using (kkFree; kkForgetful; kkCofree; kkCoforgetful)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

--            Fri            Cofor            Fri            Cofor
--         ————————▸       ◂————————       ————————▸       ◂————————       ———∙∙∙
--     C       ⊥     Kl(GF)    ⊥   CoKl(O₁C₁)  ⊥    Kl(C₂O₂)   ⊥   CoKl(O₃C₃)
--         ◂————————       ————————▸       ◂————————       ————————▸       ◂——∙∙∙
--   │   ▴    For    ▴   │   Cofri   │   ▴    For    ▴   │   Cofri   │   ▴
--   │   │           │   │           │   │           │   │           │   │
-- F │ ⊣ │ G       O₁│ ⊣ │ C₁      O₂│ ⊣ │ C₂      O₃│ ⊣ │ C₃      O₄│ ⊣ │ C₄
--   │   │           │   │           │   │           │   │           │   │
--   ▾   │   Cofor   │   ▾    Fri    ▾   │   Cofor   │   ▾    Fri    ▾   │
--         ◂————————       ————————▸       ◂————————       ————————▸       ◂——∙∙∙
--     D       ⊥    CoKl(FG)   ⊥    Kl(C₁O₁)   ⊥   CoKl(O₂C₂)  ⊥    Kl(C₃O₃)
--         ————————▸       ◂————————       ————————▸       ◂————————       ———∙∙∙
--           Cofri            For            Cofri            For

open import Categories.NaturalTransformation.Core using (NaturalTransformation)

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module ϵ = NaturalTransformation (Adjoint.counit L⊣R)
    module η = NaturalTransformation (Adjoint.unit L⊣R)
    O⊣C = KleisliAdjoints L⊣R
    P⊣D = KleisliAdjoints O⊣C
    module S = Comonad (adjoint⇒comonad L⊣R)
    module T = Monad (adjoint⇒monad L⊣R)

  open import Agda.Builtin.Equality using (_≡_; refl)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Function renaming (id to id→; _∘_ to _●_) using ()

  _ : (kkFree L⊣R) ∘F (kCofree L⊣R) ≡ record
    { F₀ = λ x → x
    -- X
    ; F₁ = λ { {A} {B} f → η.η (R.F₀ (L.F₀ B)) C.∘ R.F₁ (ϵ.η (L.F₀ B)) C.∘ R.F₁ (L.F₁ f) }
    -- η (R (L B)) ∘ R (ϵ (L B)) ∘ R (L f)
    -- ηRLB ∘ RϵLB ∘ RLf
    -- ηTB ∘ μB ∘ Tf  where  f : A → TB
    -- ηTB ∘ f*
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kCoforgetful L⊣R) ∘F (kkForgetful L⊣R) ≡ record
    { F₀ = λ x → R.F₀ (L.F₀ (R.F₀ (L.F₀ x)))
    -- TTX
    ; F₁ = λ { {A} {B} f → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (L.F₁ f) }
    -- η (R (L (R (L B)))) ∘ R (ϵ (L (R (L B)))) ∘ R (L f)
    -- ηRLRLB ∘ RϵLRLB ∘ RLf
    -- ηTTB ∘ μTB ∘ Tf  where  f : TA → TTB
    -- ηTTB ∘ f*
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kkFree L⊣R) ∘F (kCofree L⊣R) ∘F (kCoforgetful L⊣R) ∘F (kkForgetful L⊣R) ≡ record
    { F₀ = λ X → R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))
    -- TTX
    ; F₁ = λ { {A} {B} f → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ B)))))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ B)))))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (L.F₁ f))) }
    -- η (R (L (R (L (R (L B)))))) ∘ R (ϵ (L (R (L (R (L B)))))) ∘ R (L (η (R (L (R (L B)))) ∘ R (ϵ (L (R (L B)))) ∘ R (L f)))
    -- ηRLRLRLB ∘ RϵLRLRLB ∘ RLηRLRLB ∘ RLRϵLRLB ∘ RLRLf
    -- ηTTTB ∘ (μ TTB ∘ Tη TTB) ∘ TμTB ∘ TTf
    -- ηTTTB ∘ TμTB ∘ TTf  where  f : TA → TTB
    -- ηTTTB ∘ Tf*
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kCoforgetful L⊣R) ∘F (kkForgetful L⊣R) ∘F (kkFree L⊣R) ∘F (kCofree L⊣R) ≡ record
    { F₀ = λ X → R.F₀ (L.F₀ (R.F₀ (L.F₀ X)))
    -- TTX
    ; F₁ = λ { {A} {B} f → η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (ϵ.η (L.F₀ (R.F₀ (L.F₀ B)))) C.∘ R.F₁ (L.F₁ (η.η (R.F₀ (L.F₀ B)) C.∘ R.F₁ (ϵ.η (L.F₀ B)) C.∘ R.F₁ (L.F₁ f))) }
    -- η (R (L (R (L B)))) ∘ R (ϵ (L (R (L B)))) ∘ R (L (η (R (L B)) ∘ R (ϵ (L B)) ∘ R (L f)))
    -- ηRLRLB ∘ RϵLRLB ∘ RLηRLB ∘ RLRϵLB ∘ RLRLf
    -- ηTTB ∘ (μ TB ∘ Tη TB) ∘ TμB ∘ TTf
    -- ηTTB ∘ TμB ∘ TTf  where  f : A → TB
    -- ηTTB ∘ Tf*
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kkCofree L⊣R) ∘F (kFree L⊣R) ≡ record
    { F₀ = λ x → x
    -- X
    ; F₁ = λ { {A} {B} f → (L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ A))) D.∘ ϵ.η (L.F₀ (R.F₀ A)) }
    -- (L (R f) ∘ L (η (R A))) ∘ ϵ (L (R A))
    -- LRf ∘ LηRA ∘ ϵLRA
    -- Sf ∘ δA ∘ ϵSA  where  f : SA → B
    -- fᵒ ∘ ϵS
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kForgetful L⊣R) ∘F (kkCoforgetful L⊣R) ≡ record
    { F₀ = λ x → L.F₀ (R.F₀ (L.F₀ (R.F₀ x)))
    -- SSX
    ; F₁ = λ { {A} {B} f → (L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ A))))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ A)))) }
    -- (L (R f) ∘ L (η (R (L (R A))))) ∘ ϵ (L (R (L (R A))))
    -- LRf ∘ LηRLRA ∘ ϵLRLRA
    -- Sf ∘ δSA ∘ ϵSSA  where  f : SSA → SB
    -- fᵒ ∘ ϵSSA
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kkCofree L⊣R) ∘F (kFree L⊣R) ∘F (kForgetful L⊣R) ∘F (kkCoforgetful L⊣R) ≡ record
    { F₀ = λ X → L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))
    -- SSX
    ; F₁ = λ { {A} {B} f → (L.F₁ (R.F₁ ((L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ A))))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ A)))))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ A))))))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ (L.F₀ (R.F₀ A)))))) }
    -- (L (R ((L (R f) ∘ L (η (R (L (R A))))) ∘ ϵ (L (R (L (R A)))))) ∘ L (η (R (L (R (L (R A))))))) ∘ ϵ (L (R (L (R (L (R A))))))
    -- LRLRf ∘ LRLηRLRA ∘ LRϵLRLRA ∘ LηRLRLRA ∘ ϵLRLRLRA
    -- SSf ∘ SδSA ∘ (Sϵ SSA ∘ δ SSA) ∘ ϵSSSA
    -- SSf ∘ SδSA ∘ ϵSSSA  where  f : SSA → SB
    -- Sfᵒ ∘ ϵSSSA
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

  _ : (kForgetful L⊣R) ∘F (kkCoforgetful L⊣R) ∘F (kkCofree L⊣R) ∘F (kFree L⊣R) ≡ record
    { F₀ = λ X → L.F₀ (R.F₀ (L.F₀ (R.F₀ X)))
    -- SSX
    ; F₁ = λ { {A} {B} f → (L.F₁ (R.F₁ ((L.F₁ (R.F₁ f) D.∘ L.F₁ (η.η (R.F₀ A))) D.∘ ϵ.η (L.F₀ (R.F₀ A)))) D.∘ L.F₁ (η.η (R.F₀ (L.F₀ (R.F₀ A))))) D.∘ ϵ.η (L.F₀ (R.F₀ (L.F₀ (R.F₀ A)))) }
    -- (L (R ((L (R f) ∘ L (η (R A))) ∘ ϵ (L (R A)))) ∘ L (η (R (L (R A))))) ∘ ϵ (L (R (L (R A))))
    -- LRLRf ∘ LRLηRA ∘ LRϵLRA ∘ LηRLRA ∘ ϵLRLRA
    -- SSf ∘ SδA ∘ (Sϵ SA ∘ δ SA) ∘ ϵSSA
    -- SSf ∘ SδA ∘ ϵSSA  where  f : SA → B
    -- Sfᵒ ∘ ϵSSA
    ; identity = {! !} ; homomorphism = {! !} ; F-resp-≈ = {! !} }
  _ = refl

