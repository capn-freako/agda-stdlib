------------------------------------------------------------------------
-- The Agda standard library
--
-- Some bundles of linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Bundles where

open import Algebra        using (CommutativeRing)
open import Algebra.Linear.Structures
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
open import Level          using (Level; _⊔_; suc)
open import Relation.Binary

-- Abstract vector spaces.
--
-- A "vector space" is a Module with a commutative, homomorphic inner
-- product and a complete set of building blocks for mapping the space.
--
-- "Why not just use `Data.Vec`?"
--
-- Because `Data.Vec` locks us into an _array_ representation/implementation,
-- which isn't always the best when trying to avail one's self of the
-- myriad options now available for massively parallel computation
-- acceleration in hardware (i.e. - silicon).
--
-- "Okay; so, then, why not just invent a brand new data type?"
--
-- Because people are used to working with "vectors", and we don't want
-- to rock their World too much ... yet. ;-)
record VectorSpace
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where

  constructor mkVS

  open CommutativeRing ring renaming (Carrier  to S)   public
  open Module          mod  renaming (Carrierᴹ to V)   public

  field
    isBasis       : IsBasis mod
    isVectorSpace : IsVectorSpace mod isBasis

  open IsBasis       isBasis       public
  open IsVectorSpace isVectorSpace public

  -- Linear maps from vectors to scalars.
  V⊸S = LinearMap mod ⟨module⟩

  -- Equivalent vector generator.
  v : V⊸S → V
  v lm = vgen (LinearMap.f lm) basisSet

  open Setoid (≈ᴸ-setoid mod ⟨module⟩) public using () renaming
    ( _≈_ to _≈ᴸ_
    ; _≉_ to _≉ᴸ_
    )

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

