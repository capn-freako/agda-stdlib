------------------------------------------------------------------------
-- The Agda standard library
--
-- Vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.VectorSpace.Core where

import Algebra.Module.Morphism.Structures as MorphismStructures

open import Algebra        using (CommutativeRing)
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
open import Data.Fin       using (Fin)
open import Data.List
open import Data.Nat       using (ℕ)
open import Data.Product
open import Function
open import Level          using (Level; _⊔_; suc)
open import Relation.Binary
open import Relation.Binary.ExtensionalEquivalence
open import Relation.Binary.Reasoning.MultiSetoid

------------------------------------------------------------------------
-- Abstract vector space.
--
-- A "vector space" is a `Module` with a commutative, homomorphic inner
-- product and a complete set of building blocks for mapping the space.
record VectorSpace
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where
  
  constructor mkVS

  open CommutativeRing ring renaming (Carrier  to A)   public
  open Module          mod  renaming (Carrierᴹ to V)   public
  open MorphismStructures.ModuleMorphisms mod ⟨module⟩ public

  vscale : (V → A) → V → V
  vscale f = uncurry _*ₗ_ ∘ < f , id >

  vgen : (V → A) → List V → V
  vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ
  
  infix 7 _∙_
  field
    _∙_           : V → V → A
    -- ToDo: `List` => `Foldable Functor`.
    basisSet      : List V
    basisComplete : ∀ {a : V} →
                    a ≈ᴹ vgen (a ∙_) basisSet

    -- ToDo: Can these be unified, by using one of the
    -- existing algebraic structures?
    -- I'm only finding things that are predicated upon: `A → A → A`, or
    -- `A → B`; nothing for: `A → A → B`.
    ∙-comm      : ∀ {a b}     → a ∙ b ≈ b ∙ a
    ∙-distrib-+ : ∀ {a b c}   → a ∙ (b +ᴹ c)    ≈ (a ∙ b) + (a ∙ c)
    ∙-comm-*ₗ   : ∀ {s} {a b} → a ∙ (s *ₗ b)    ≈ s * (a ∙ b)
    ∙-comm-*ᵣ   : ∀ {s} {a b} → a ∙ (b *ᵣ s)    ≈ (a ∙ b) * s  -- Prove?
    ∙-congˡ     : ∀ {a b c}   → b ≈ᴹ c → a ∙ b ≈ a ∙ c
    ∙-idˡ       : ∀ {a}       → 0ᴹ ∙ a ≈ 0#
    ∙-homo-⁻¹    : ∀ {a b}     → a ∙ (-ᴹ b) ≈ - (a ∙ b)

  ∙-distrib-+ʳ : ∀ {a b c} → (b +ᴹ c) ∙ a ≈ (b ∙ a) + (c ∙ a)
  ∙-distrib-+ʳ {a} {b} {c} = begin⟨ setoid ⟩
    (b +ᴹ c) ∙ a      ≈⟨ ∙-comm ⟩
    a ∙ (b +ᴹ c)      ≈⟨ ∙-distrib-+ ⟩
    (a ∙ b) + (a ∙ c) ≈⟨ +-cong ∙-comm ∙-comm ⟩
    (b ∙ a) + (c ∙ a) ∎
    
  ∙-comm-*ₗʳ : ∀ {s} {a b} → (s *ₗ b) ∙ a ≈ s * (b ∙ a)
  ∙-comm-*ₗʳ {s} {a} {b} = begin⟨ setoid ⟩
    (s *ₗ b) ∙ a ≈⟨ ∙-comm ⟩
    a ∙ (s *ₗ b) ≈⟨ ∙-comm-*ₗ ⟩
    s * (a ∙ b)  ≈⟨ *-congˡ ∙-comm ⟩
    s * (b ∙ a)  ∎

  ∙-comm-*ᵣʳ : ∀ {s} {a b} → (b *ᵣ s) ∙ a ≈ s * (b ∙ a)
  ∙-comm-*ᵣʳ {s} {a} {b} = begin⟨ setoid ⟩
    (b *ᵣ s) ∙ a ≈⟨ ∙-comm ⟩
    a ∙ (b *ᵣ s) ≈⟨ ∙-comm-*ᵣ ⟩
    (a ∙ b) * s  ≈⟨ *-congʳ ∙-comm ⟩
    (b ∙ a) * s  ≈⟨ *-comm (b ∙ a) s ⟩
    s * (b ∙ a)  ∎

  ∙-congʳ : ∀ {a b c} → b ≈ᴹ c → b ∙ a ≈ c ∙ a
  ∙-congʳ {a} {b} {c} b≈c = begin⟨ setoid ⟩
    b ∙ a ≈⟨ ∙-comm ⟩
    a ∙ b ≈⟨ ∙-congˡ b≈c ⟩
    a ∙ c ≈⟨ ∙-comm ⟩
    c ∙ a ∎

  ∙-cong : ∀ {a b c d} → a ≈ᴹ c → b ≈ᴹ d → a ∙ b ≈ c ∙ d
  ∙-cong {a} {b} {c} {d} a≈c b≈d = begin⟨ setoid ⟩
    a ∙ b ≈⟨ ∙-congˡ b≈d ⟩
    a ∙ d ≈⟨ ∙-congʳ a≈c ⟩
    c ∙ d ∎
  
  ∙-idʳ : ∀ {a} → a ∙ 0ᴹ ≈ 0#
  ∙-idʳ {a} = begin⟨ setoid ⟩
    a ∙ 0ᴹ ≈⟨ ∙-comm ⟩
    0ᴹ ∙ a ≈⟨ ∙-idˡ ⟩
    0#     ∎

  ∙-homo-⁻¹ˡ : ∀ {a b} → (-ᴹ b) ∙ a ≈ - (b ∙ a)
  ∙-homo-⁻¹ˡ {a} {b} = begin⟨ setoid ⟩
    (-ᴹ b) ∙ a ≈⟨ ∙-comm ⟩
    a ∙ (-ᴹ b) ≈⟨ ∙-homo-⁻¹ ⟩
    - (a ∙ b)  ≈⟨ -‿cong ∙-comm ⟩
    - (b ∙ a)  ∎

  vscale-cong : ∀ f → Congruent _≈ᴹ_ _≈_ f → Congruent _≈ᴹ_ _≈ᴹ_ (vscale f)
  vscale-cong f f-cong {x} {y} x≈y = begin⟨ ≈ᴹ-setoid ⟩
    vscale f x ≡⟨⟩
    f x *ₗ x   ≈⟨ *ₗ-congʳ (f-cong x≈y) ⟩
    f y *ₗ x   ≈⟨ *ₗ-congˡ x≈y ⟩
    f y *ₗ y   ≡⟨⟩
    vscale f y ∎

  V⊸A = LinearMap mod ⟨module⟩ -- Linear maps from vectors to scalars.
  
  -- Equivalent vector generator.
  lmToVec : V⊸A → V
  lmToVec lm = vgen (LinearMap.f lm) basisSet

  -- ToDo: equivalent matrix generator? How to even define the type?
  -- lmToMat : V⊸V → ?
  -- Maybe change type of `V⊸V` to:
  -- V⊸V = List V⊸A
  -- And then:
  -- -- Equivalent matrix generator.
  -- lmToMat : V⊸V → List V
  -- lmToMat []         = []
  -- lmToMat (lm ∷ lms) = lmToVec lm ∷ lmToMat lms

  -- ToDo: How to generate `List V⊸A` from `LinearMap mod mod`?
  -- T(x) = y; express `x` in terms of basisSet and make use of linearity.
  -- (May require transposition.)
  -- f : V → V; f linear.
  -- f v                                                               =⟨ basisComplete ⟩
  -- f (vgen (v ∙_) basisSet)                                          =⟨ vgen ⟩
  -- f (foldr (_+ᴹ_ ∘ vscale (v ∙_)) 0ᴹ basisSet)                      =⟨ vscale ⟩
  -- f (foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < (v ∙_) , id >) 0ᴹ basisSet)     =⟨ ? ⟩
  -- foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < (v ∙_) , id >) 0ᴹ (map f basisSet) =⟨ ? ⟩
  -- vgen (v ∙_) (map f basisSet)                                      ∎
  
  open Setoid (≈ᴸ-setoid mod ⟨module⟩) using () renaming
    ( _≈_ to _≈ˢ_
    ; _≉_ to _≉ˢ_
    ) public
