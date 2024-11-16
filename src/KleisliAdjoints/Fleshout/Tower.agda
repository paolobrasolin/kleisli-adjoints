{-# OPTIONS --without-K #-}
module KleisliAdjoints.Fleshout.Tower where

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


  open import Agda.Builtin.Equality using (_≡_; refl)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Categories.NaturalTransformation.Core using (NaturalTransformation)

  KA0 = F⊣G
  KA1 = KleisliAdjoints F⊣G
  KA2 = KleisliAdjoints KA1

  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  module G∘F = Functor (G ∘F F)
  module F∘G = Functor (F ∘F G)
  open import Function.Base using (_∘_)

  module ϵ = NaturalTransformation (Adjoint.counit F⊣G)
  module η = NaturalTransformation (Adjoint.unit F⊣G)

  _ : Functor.F₀ (Forgetful (adjoint⇒monad KA2)) ≡ λ x → G.F₀ (F.F₀ x)
  _ = refl
  _ : Functor.F₀ (Coforgetful (adjoint⇒comonad KA1)) ≡ λ x → G.F₀ (F.F₀ x)
  _ = refl
  _ : (Functor.F₀ (Coforgetful (adjoint⇒comonad KA1))) ∘ (Functor.F₀ (Forgetful (adjoint⇒monad KA2))) ≡ λ x → G.F₀ (F.F₀ (G.F₀ (F.F₀ x)))
  _ = refl

  -- _ : Functor.F₁ (Forgetful (adjoint⇒monad KA2)) ≡ ?
  -- _ = refl
  lemmino : {X Y : C.Obj} {f : G.F₀ (F.F₀ X) C.⇒ G.F₀ (F.F₀ (G.F₀ (F.F₀ Y)))} → (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ G.F₁ (F.F₁ ((G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ G.F₁ (F.F₁ C.id)) C.∘ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (F.F₁ (η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ _)))) C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))) C.∘ C.id))) C.∘ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) C.∘ G.F₁ (F.F₁ (η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))) D.∘ F.F₁ ((G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (F.F₁ C.id)) C.∘ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))))) C.∘ G.F₁ (F.F₁ (η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ (D.id D.∘ F.F₁ (G.F₁ ((ϵ.η (F.F₀ (G.F₀ (F.F₀ _))) D.∘ F.F₁ f D.∘ ϵ.η (F.F₀ (G.F₀ (F.F₀ _)))) D.∘ F.F₁ (G.F₁ D.id) D.∘ F.F₁ (η.η (G.F₀ (F.F₀ _))))) D.∘ F.F₁ (η.η (G.F₀ (F.F₀ _)))) C.∘ η.η (G.F₀ (F.F₀ _))))) C.∘ C.id) D.∘ ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _))))))))) C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))))) C.∘ G.F₁ D.id C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ _)))) C.≈ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ Y)))) C.∘ G.F₁ (F.F₁ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ Y))))))) C.∘ G.F₁ (F.F₁ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ Y))))) D.∘ F.F₁ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ Y)))))) C.∘ G.F₁ (F.F₁ (G.F₁ (F.F₁ (G.F₁ (ϵ.η (F.F₀ (G.F₀ (F.F₀ Y))) D.∘ F.F₁ f)) D.∘ F.F₁ (η.η (G.F₀ (F.F₀ X)))) C.∘ η.η (G.F₀ (F.F₀ X)))))))) C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ (G.F₀ (F.F₀ X)))))) C.∘ η.η (G.F₀ (F.F₀ (G.F₀ (F.F₀ X))))
  lemmino = begin
    -- (G (ϵ (F (G (F _)))) ∘ G (F ((G (ϵ (F (G (F _))))) ∘ (G (ϵ (F (G (F (G (F _)))))) ∘ G (F (η (G (F (G (F _)))) ∘ G (ϵ (F (G (F _)))) ∘ η (G (F (G (F _)))))))))) ∘ (G (ϵ (F (G (F (G (F (G (F _)))))))) ∘ G (F (η (G (F (G (F (G (F _)))))) ∘ G (ϵ (F (G (F (G (F _))))) ∘ F ((G (ϵ (F (G (F (G (F _))))))) ∘ (G (ϵ (F (G (F (G (F (G (F _)))))))) ∘ G (F (η (G (F (G (F (G (F _)))))) ∘ G (F (G ((ϵ (F (G (F _))) ∘ F f ∘ ϵ (F (G (F _)))) ∘ F (η (G (F _))))) ∘ F (η (G (F _)))) ∘ η (G (F _)))))) ∘ ϵ (F (G (F (G (F _)))))) ∘ η (G (F (G (F (G (F _))))))))) ∘ η (G (F (G (F (G (F _)))))) ∘ η (G (F (G (F _))))
    _ ≈⟨ ( refl⟩∘⟨ G∘F.F-resp-≈ ( elimʳ G∘F.identity ⟩∘⟨ elimʳ C.Equiv.refl ) ) ⟩∘⟨ ( refl⟩∘⟨ G∘F.F-resp-≈ ( refl⟩∘⟨ G.F-resp-≈ ( D.HomReasoning.refl⟩∘⟨ F.F-resp-≈ ( elimʳ G∘F.identity ⟩∘⟨ (elimʳ C.Equiv.refl ○ ( refl⟩∘⟨ G∘F.F-resp-≈ ( refl⟩∘⟨ G.F-resp-≈ ( MR.elimˡ D D.Equiv.refl D.HomReasoning.○ ( F∘G.F-resp-≈ (MR.elim-center D F∘G.identity) D.HomReasoning.⟩∘⟨refl ) ) ⟩∘⟨refl ) ) ) ) D.HomReasoning.⟩∘⟨refl ) ⟩∘⟨refl ) ) ⟩∘⟨ elim-center G.identity ⟩
    -- GϵFGF_ ∘ GFGϵFGF_ ∘ (GFGϵFGFGF_ ∘ GFGFηGFGF_) ∘ (GFGFGϵFGF_ ∘ GFGFηGFGF_) ∘ (GϵFGFGFGF_ ∘ GFηGFGFGF_) ∘ GFGϵFGFGF_ ∘ GFGFGϵFGFGF_ ∘ (GFGFGϵFGFGFGF_ ∘ GFGFGFηGFGFGF_) ∘ GFGFGFGFGϵFGF_ ∘ GFGFGFGFGFf ∘ (GFGFGFGFGϵFGF_ ∘ GFGFGFGFGFηGF_) ∘ GFGFGFGFηGF_ ∘ GFGFGFηGF_ ∘ (GFGϵFGFGF_ ∘ GFηGFGFGF_) ∘ ηGFGFGF_ ∘ ηGFGF_
    _ ≈⟨ ( refl⟩∘⟨ G∘F.F-resp-≈ ( refl⟩∘⟨ ( C.Equiv.sym G.homomorphism ○ ( G.F-resp-≈ ( D.HomReasoning.refl⟩∘⟨ F.F-resp-≈ ( elimʳ (Adjoint.zag F⊣G) ) ) ) ) ○ ( elimʳ (G.F-resp-≈ (Adjoint.zig F⊣G) ○ G.identity) ) ) ) ⟩∘⟨ ( C.Equiv.sym G.homomorphism ○ G.F-resp-≈ ( ( D.HomReasoning.refl⟩∘⟨ F.homomorphism ) D.HomReasoning.○ (MR.cancelˡ D (Adjoint.zig F⊣G)) D.HomReasoning.○ F.F-resp-≈ (pushˡ (G.F-resp-≈ (D.Equiv.sym D.assoc) ○ G.homomorphism ) ○ elimʳ (Adjoint.zag F⊣G) ○ G.F-resp-≈ (D.HomReasoning.refl⟩∘⟨ F.F-resp-≈ (refl⟩∘⟨ (C.Equiv.sym G.homomorphism ○ G.F-resp-≈ (D.HomReasoning.refl⟩∘⟨ F.homomorphism D.HomReasoning.○ MR.cancelˡ D (Adjoint.zig F⊣G) D.HomReasoning.○ F.F-resp-≈ (G.F-resp-≈ (F∘G.F-resp-≈ (( D.∘-resp-≈ˡ D.sym-assoc D.HomReasoning.○ D.assoc) D.HomReasoning.○ MR.elimʳ D (Adjoint.zig F⊣G)) D.HomReasoning.⟩∘⟨refl) ⟩∘⟨refl))))) ) ) ) ⟩∘⟨refl ⟩
    -- GϵFGFY ∘ GFGϵFGFY ∘ GFGϵFGFGFY ∘ GFGFGϵFGFGFY ∘ GFGFGFGFGϵFGFY ∘ GFGFGFGFGFf ∘ GFGFGFGFηGFX ∘ GFGFGFηGFX ∘ ηGFGFGFX ∘ ηGFGFX
    _ ≈⟨ {! !} ⟩
    -- GϵFGF_ ∘ GFGϵFGF_ ∘ GFGϵFGFGF_ ∘ GFGFGFf ∘ ηGFGFGF_ ∘ ηGFGF_
    _ ∎
    where open C.HomReasoning
          open MR C

