{-# OPTIONS --without-K #-}
module KleisliAdjoints.Fleshout.Tower where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.Adjoint.Construction.Kleisli using (Free⊣Forgetful; Free; Forgetful)
open import Categories.Adjoint.Construction.CoKleisli using (Forgetful⊣Cofree; Cofree) renaming (Forgetful to Coforgetful)
open import Categories.Monad using (Monad)
open import Categories.Comonad using (Comonad)

open import KleisliAdjoints using (Contextualise; Operationalise; KleisliAdjoints)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ {F : Functor C D} {G : Functor D C} (F⊣G : F ⊣ G) where

  -- An adjunction induces a (co)monad on the (co)domain of the left adjoint:
  GF = adjoint⇒monad F⊣G
  _ : Endofunctor C
  _ = Monad.F GF
  FG = adjoint⇒comonad F⊣G
  _ : Endofunctor D
  _ = Comonad.F FG
  -- A (co)monad induces an adjunction with its (co)Kleisli category:
  _ : Free GF ⊣ Forgetful GF
  _ = Free⊣Forgetful GF
  _ : Coforgetful FG ⊣ Cofree FG
  _ = Forgetful⊣Cofree FG
  -- The construction induces an adjunction between the Kleisli and coKleisli categories:
  _ : Functor (CoKleisli FG) (Kleisli GF)
  _ = Operationalise F⊣G
  _ : Functor (Kleisli GF) (CoKleisli FG)
  _ = Contextualise F⊣G
  _ : Operationalise F⊣G ⊣ Contextualise F⊣G
  _ = KleisliAdjoints F⊣G

  -- The adjunction induced by this construction "swaps" the direction of the initial adjunction.
  -- Noticing this and book-keeping with the facts above, we can iterate the construction as follows:
  --
  --            Fri             For             Fri             For
  --         ————————▸       ◂————————       ————————▸       ◂————————       ———∙∙∙
  --     C       ⊥     Kl(GF)    ⊥   CoKl(O₁C₁)  ⊥    Kl(C₂O₂)   ⊥   CoKl(O₃C₃)
  --         ◂————————       ————————▸       ◂————————       ————————▸       ◂——∙∙∙
  --   │   ▴    For    ▴   │    Cof    │   ▴    For    ▴   │    Cof    │   ▴
  --   │   │           │   │           │   │           │   │           │   │
  -- F │ ⊣ │ G       O₁│ ⊣ │ C₁      O₂│ ⊣ │ C₂      O₃│ ⊣ │ C₃      O₄│ ⊣ │ C₄
  --   │   │           │   │           │   │           │   │           │   │
  --   ▾   │    For    │   ▾    Fri    ▾   │    For    │   ▾    Fri    ▾   │
  --         ◂————————       ————————▸       ◂————————       ————————▸       ◂——∙∙∙
  --     D       ⊥    CoKl(FG)   ⊥    Kl(C₁O₁)   ⊥   CoKl(O₂C₂)  ⊥    Kl(C₃O₃)
  --         ————————▸       ◂————————       ————————▸       ◂————————       ———∙∙∙
  --            Cof             For             Cof             For

