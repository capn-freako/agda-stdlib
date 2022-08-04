------------------------------------------------------------------------
-- The Agda standard library
--
-- Some linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Structures where

open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Data.List                           using (List; foldr)
open import Data.Product
open import Function
open import Level                               using (Level; _⊔_; suc)
open import Relation.Binary.Reasoning.MultiSetoid

module _
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  where

  open CommutativeRing ring renaming (Carrier  to S)
  open Module          mod  renaming (Carrierᴹ to V)

  -- A set of "vectors" forms a basis for a space iff it is complete
  -- under some inner product.
  record IsBasis : Set (suc (ℓm ⊔ m ⊔ r)) where

    vscale : (V → S) → V → V
    vscale f = uncurry _*ₗ_ ∘ < f , id >

    vgen : (V → S) → List V → V
    vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ

    infix 7 _∙_
    field
      _∙_           : V → V → S
      basisSet      : List V                     -- ToDo: List => Foldable Functor
      basisComplete : ∀ {a : V} →
                      a ≈ᴹ vgen (a ∙_) basisSet


  -- The space mapped (i.e. - represented) by a basis constitutes a
  -- vector space iff the inner product has certain properties.
  record IsVectorSpace
    (isBasis : IsBasis)
    : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r))
    where

    open IsBasis isBasis

    field
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
