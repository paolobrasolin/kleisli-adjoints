import Level
open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)

module KleisliAdjoints {o l e o' l' e'} {C : Category o l e} {D : Category o' l' e'} {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where

open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.NaturalTransformation as NT using (ntHelper)

import Categories.Morphism.Reasoning as MR


pollo : Functor (Kleisli (adjoint⇒monad Adj)) (CoKleisli (adjoint⇒comonad Adj))
pollo = record
  { F₀ = F.F₀
  ; F₁ = let ε = Adj.counit.η in
       λ { f → ε (F.F₀ _) D.∘ (F.F₁ f) D.∘ ε (F.F₀ _) }
  ; identity = λ {A} → cancelˡ Adj.zig
    -- begin
    -- Adj.counit.η (F.F₀ A) D.∘ F.F₁ (Adj.unit.η A) D.∘ Adj.counit.η (F.F₀ A) ≈⟨ cancelˡ Adj.zig ⟩
    -- Adj.counit.η (F.F₀ A)                                                   ∎
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
  ; F-resp-≈ = λ { x → refl⟩∘⟨ (F.F-resp-≈ x ⟩∘⟨refl) }
  } where module F = Functor F
          module G = Functor G
          module C = Category C
          module D = Category D
          module Adj = Adjoint Adj
          open D.HomReasoning
          open MR D

gallo : Functor (CoKleisli (adjoint⇒comonad Adj)) (Kleisli (adjoint⇒monad Adj))
gallo = record
  { F₀ = G.F₀
  ; F₁ = λ { f → Adj.unit.η (G.F₀ _) C.∘ (G.F₁ f) C.∘ Adj.unit.η (G.F₀ _) }
  ; identity = λ {A} → begin
    _ ≈⟨ elimʳ Adj.zag ⟩
    _ ∎
  ; homomorphism = {! !}
  ; F-resp-≈ = λ { x → refl⟩∘⟨ (G.F-resp-≈ x ⟩∘⟨refl) }
  } where module G = Functor G
          module C = Category C
          module Adj = Adjoint Adj
          open C.HomReasoning
          open MR C

gallo⊣pollo : gallo ⊣ pollo
gallo⊣pollo = record
  { unit = ntHelper (let open D.HomReasoning
                         open MR D in record
    { η = λ X → D.id
    ; commute = λ { {X} {Y} f → begin
        _ ≈⟨ D.identityˡ ⟩
        _ ≈˘⟨ MR.cancelInner D (zig Adj) ⟩
        _ ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩
        _ ≈⟨ refl⟩∘⟨ F.F-resp-≈ (commute (unit Adj) _) ⟩
        _ ≈˘⟨ refl⟩∘⟨ D.Equiv.sym F.homomorphism ⟩
        _ ≈˘⟨ D.∘-resp-≈ˡ D.sym-assoc ○ D.assoc ⟩ -- assoc²βγ
        _ ≈˘⟨ MR.pullʳ D (sym-commute (counit Adj) _) ⟩∘⟨refl ⟩
        _ ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈˘⟨ MR.elimˡ D (zig Adj) ⟩∘⟨refl ⟩
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
    ; commute = λ { f → {!    !} }
    })
  ; zig = λ { {A} → let open C.HomReasoning
                        open MR C in
            begin {!   !} ≈⟨ (refl⟩∘⟨ elim-center G.identity) ⟩
                  {!   !} ≈⟨ ({!!} ⟩∘⟨refl) ⟩
                  {!   !} ≈⟨ {!   !} ⟩
                  {!   !} ∎ }
  ; zag = λ {B} → {!   !}
  } where module F = Functor F
          module G = Functor G
          module F∘G = Functor (F ∘F G)
          open Adjoint
          open NT.NaturalTransformation
          module C = Category C
          module D = Category D
