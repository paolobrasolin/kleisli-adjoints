{-# OPTIONS --without-K --safe #-}
module KleisliAdjoints where

open import Level

open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.NaturalTransformation using (ntHelper)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module Adj = Adjoint Adj
    module G∘F = Functor (G ∘F F)
    module F∘G = Functor (F ∘F G)
    GF = adjoint⇒monad Adj
    FG = adjoint⇒comonad Adj

  Contextualise : Functor (Kleisli GF) (CoKleisli FG)
  Contextualise = record
    { F₀ = F.F₀
    ; F₁ = let ε = Adj.counit.η in λ { f → ε (F.F₀ _) D.∘ (F.F₁ f) D.∘ ε (F.F₀ _) }
    ; identity = cancelˡ Adj.zig
    ; homomorphism = begin
      _ ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
      _ ≈⟨ D.∘-resp-≈ʳ D.assoc ○ D.sym-assoc ⟩ -- TODO: use assoc²δγ
      _ ≈⟨ D.sym-assoc ⟩∘⟨refl ⟩
      _ ≈⟨ Adj.counit.commute _ ⟩∘⟨refl ⟩∘⟨refl ⟩
      _ ≈⟨ D.assoc ⟩∘⟨refl ⟩
      _ ≈⟨ ( refl⟩∘⟨ Adj.counit.commute _ ) ⟩∘⟨refl ⟩
      _ ≈⟨ D.sym-assoc ⟩∘⟨refl ⟩
      _ ≈⟨ D.assoc ○ D.∘-resp-≈ʳ D.sym-assoc ⟩ -- TODO: use assoc²γδ
      _ ≈⟨ refl⟩∘⟨ pullʳ (D.Equiv.sym (Adj.counit.commute _)) ⟩
      _ ≈⟨ refl⟩∘⟨ pullˡ (D.Equiv.sym (Adj.counit.commute _)) ⟩
      _ ≈⟨ introʳ F.identity ⟩
      _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (C.Equiv.sym Adj.zag) ⟩
      _ ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
      _ ≈⟨ ( refl⟩∘⟨ D.assoc) ⟩∘⟨refl ⟩
      _ ≈⟨ D.sym-assoc ⟩∘⟨refl ⟩
      _ ≈⟨ D.assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
      _ ≈⟨ D.assoc ⟩
      _ ≈⟨ refl⟩∘⟨ (D.sym-assoc ○ D.∘-resp-≈ˡ D.assoc) ⟩ -- TODO: use assoc²γβ
      _ ≈⟨ refl⟩∘⟨ pullˡ (D.Equiv.sym F.homomorphism) ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (C.Equiv.sym G.homomorphism) ⟩∘⟨refl ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ D.Equiv.sym F.homomorphism ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (C.Equiv.sym G.homomorphism) ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (G.F-resp-≈ D.assoc) ⟩∘⟨refl ⟩
      _ ≈⟨ refl⟩∘⟨ D.Equiv.refl ⟩∘⟨refl ⟩
      _ ∎
    ; F-resp-≈ = λ { x → refl⟩∘⟨ F.F-resp-≈ x ⟩∘⟨refl }
    } where open D.HomReasoning
            open MR D

  Operationalise : Functor (CoKleisli FG) (Kleisli GF)
  Operationalise = record
    { F₀ = G.F₀
    ; F₁ = let η = Adj.unit.η in λ { f → η (G.F₀ _) C.∘ (G.F₁ f) C.∘ η (G.F₀ _) }
    ; identity = elimʳ Adj.zag
    ; homomorphism = begin
        _ ≈⟨ refl⟩∘⟨ ((G.homomorphism ○ (refl⟩∘⟨ G.homomorphism)) ⟩∘⟨refl) ⟩
        _ ≈⟨ refl⟩∘⟨ (C.sym-assoc ⟩∘⟨refl) ⟩
        _ ≈⟨ refl⟩∘⟨ (MR.pullʳ C (Adj.unit.sym-commute _) ) ⟩
        _ ≈⟨ refl⟩∘⟨ C.assoc ⟩
        _ ≈⟨ refl⟩∘⟨ MR.pull-center C (Adj.unit.sym-commute _) ⟩
        _ ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ C.assoc) ⟩
        _ ≈⟨ pullˡ (Adj.unit.commute _) ⟩
        _ ≈⟨ C.assoc ○ C.∘-resp-≈ʳ C.sym-assoc ⟩ -- assoc²γδ
        _ ≈⟨ refl⟩∘⟨ Adj.unit.commute _ ⟩∘⟨refl ⟩
        _ ≈⟨ C.∘-resp-≈ʳ C.assoc ○ C.sym-assoc ⟩ -- assoc²δγ
        _ ≈˘⟨ G∘F.homomorphism ⟩∘⟨refl ⟩
        _ ≈˘⟨ G.F-resp-≈ (MR.cancelˡ D Adj.zig) ⟩∘⟨refl ⟩
        _ ≈˘⟨ G.F-resp-≈ (D.∘-resp-≈ʳ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ G.homomorphism ⟩∘⟨refl ⟩
        _ ∎
    ; F-resp-≈ = λ { x → refl⟩∘⟨ G.F-resp-≈ x ⟩∘⟨refl }
    } where open C.HomReasoning
            open MR C

  KleisliAdjoints : Operationalise ⊣ Contextualise
  KleisliAdjoints = record
    { unit = ntHelper (let open D.HomReasoning
                           open MR D in record
      { η = λ X → D.id
      ; commute = λ { {X} {Y} f → begin
          _ ≈⟨ D.identityˡ ⟩
          _ ≈˘⟨ MR.cancelInner D Adj.zig ⟩
          _ ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩
          _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (Adj.unit.commute _) ⟩
          _ ≈˘⟨ refl⟩∘⟨ D.Equiv.sym F.homomorphism ⟩
          _ ≈˘⟨ D.∘-resp-≈ˡ D.sym-assoc ○ D.assoc ⟩ -- assoc²βγ
          _ ≈˘⟨ MR.pullʳ D (Adj.counit.sym-commute _) ⟩∘⟨refl ⟩
          _ ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
          _ ≈˘⟨ MR.elimˡ D Adj.zig ⟩∘⟨refl ⟩
          _ ≈˘⟨ (D.∘-resp-≈ʳ D.assoc ○ D.sym-assoc) ⟩∘⟨refl ⟩ -- assoc²δγ
          _ ≈˘⟨ (refl⟩∘⟨ (F.homomorphism ⟩∘⟨refl)) ⟩∘⟨refl ⟩
          _ ≈˘⟨ refl⟩∘⟨ MR.elimˡ D F∘G.identity ⟩
          _ ≈˘⟨ refl⟩∘⟨ MR.elimˡ D F.identity ⟩
          _ ≈⟨ MR.elim-center D F.identity ⟩
          _  ∎ }
      })
    ; counit = ntHelper (let open C.HomReasoning
                             open MR C in record
      { η = λ X → C.id
      ; commute = λ { f → begin
        _ ≈⟨ elimʳ G∘F.identity ⟩∘⟨refl ⟩
        _ ≈⟨ cancelˡ Adj.zag ⟩
        _ ≈⟨ pushˡ G.homomorphism ⟩
        _ ≈⟨ refl⟩∘⟨ pushˡ G.homomorphism ⟩
        _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Adj.zag ⟩
        _ ≈⟨ C.sym-assoc ⟩
        _ ∎  }
      })
    ; zig = λ { {A} →
      let open C.HomReasoning
          open MR C in
      begin
        _ ≈⟨ refl⟩∘⟨ elim-center G.identity ⟩
        _ ≈⟨ elimʳ G∘F.identity ⟩∘⟨refl ⟩
        _ ≈⟨ cancelˡ Adj.zag ⟩
        _ ∎ }
    ; zag = λ { {B} →
      let open D.HomReasoning
          open MR D in
      begin
        _ ≈⟨ elim-center F∘G.identity ⟩
        _ ≈⟨ elim-center F.identity ⟩∘⟨refl ⟩
        _ ≈⟨ cancelʳ Adj.zig ⟩
        _ ∎ }
    }

