import Level
open import Categories.Category using (Category; _[_∘_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Adjoint using (Adjoint; _⊣_)

module KleisliAdjoints {o l e o' l' e'} {C : Category o l e} {D : Category o' l' e'} {F : Functor C D} {G : Functor D C} (Adj : F ⊣ G) where

open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Construction.CoKleisli using (CoKleisli)
open import Categories.Adjoint.Properties using (adjoint⇒monad; adjoint⇒comonad)
open import Categories.NaturalTransformation as NT using (ntHelper)

open import Categories.Adjoint.Construction.Kleisli
import Categories.Morphism.Reasoning as MR

GF = adjoint⇒monad Adj
FG = adjoint⇒comonad Adj

pollo : Functor (Kleisli GF) (CoKleisli FG)
pollo = record
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
  ; F₁ = let η = Adj.unit.η in λ { f → η (G.F₀ _) C.∘ (G.F₁ f) C.∘ η (G.F₀ _) }
  ; identity = elimʳ Adj.zag
  ; homomorphism = begin 
      _ ≈⟨ refl⟩∘⟨ ((G.homomorphism ○ (refl⟩∘⟨ G.homomorphism)) ⟩∘⟨refl) ⟩
      _ ≈⟨ refl⟩∘⟨ (C.sym-assoc ⟩∘⟨refl) ⟩
      _ ≈⟨ refl⟩∘⟨ (MR.pullʳ C (Adj.unit.sym-commute _) ) ⟩
      _ ≈⟨ refl⟩∘⟨ C.assoc ⟩
      _ ≈⟨ refl⟩∘⟨ MR.pull-center C (Adj.unit.sym-commute _) ⟩
      _ ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ C.assoc) ⟩
      {! !} ≈⟨ {! !} ⟩ -- hGZ . Gg . hGY . Gf . hGX 
      {! !} ≈˘⟨ {!  !} ⟩∘⟨refl ⟩ -- (GFGg . GFhGY) . hGY . Gf . hGX
      _ ≈˘⟨ G∘F.homomorphism ⟩∘⟨refl ⟩
      _ ≈˘⟨ G.F-resp-≈ (MR.cancelˡ D Adj.zig) ⟩∘⟨refl ⟩
      _ ≈˘⟨ G.F-resp-≈ (D.∘-resp-≈ʳ F.homomorphism) ⟩∘⟨refl ⟩
      _ ≈⟨ G.homomorphism ⟩∘⟨refl ⟩
      {! !} ∎  
  ; F-resp-≈ = λ { x → refl⟩∘⟨ G.F-resp-≈ x ⟩∘⟨refl }
  } where module G = Functor G
          module C = Category C
          module D = Category D
          module F = Functor F
          module G∘F = Functor (G ∘F F)
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
    ; commute = λ { f → begin
      _ ≈⟨ elimʳ G∘F.identity ⟩∘⟨refl ⟩
      _ ≈⟨ cancelˡ (zag Adj) ⟩
      _ ≈⟨ pushˡ G.homomorphism ⟩
      _ ≈⟨ refl⟩∘⟨ pushˡ G.homomorphism ⟩
      _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ zag Adj ⟩
      _ ≈⟨ C.sym-assoc ⟩
      _ ∎  }
    })
  ; zig = λ { {A} →
    let open C.HomReasoning
        open MR C in
    begin
      _ ≈⟨ refl⟩∘⟨ elim-center G.identity ⟩
      _ ≈⟨ elimʳ G∘F.identity ⟩∘⟨refl ⟩
      _ ≈⟨ cancelˡ (zag Adj) ⟩
      _ ∎ }
  ; zag = λ { {B} →
    let open D.HomReasoning
        open MR D in
    begin
      _ ≈⟨ elim-center F∘G.identity ⟩
      _ ≈⟨ elim-center F.identity ⟩∘⟨refl ⟩
      _ ≈⟨ cancelʳ (zig Adj) ⟩
      _ ∎ }
  } where module F = Functor F
          module G = Functor G
          module F∘G = Functor (F ∘F G)
          module G∘F = Functor (G ∘F F)
          open Adjoint
          open NT.NaturalTransformation
          module C = Category C
          module D = Category D


