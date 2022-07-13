------------------------------------------------------------------------
-- The Agda standard library
--
-- A denotation for `Data.Vec` using `Data.VectorSpace`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Denotation where

open import Algebra             using (CommutativeRing)
open import Algebra.Module.Morphism.Bundles
open import Data.Nat.Base       hiding (_⊔_; _+_; _*_)
open import Data.Vec.Base
import      Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecFuncSetoid
open import Data.Vec.Instances
import      Data.Vec.Properties.Equivalence                     as VecEq
import      Data.Vec.Relation.Binary.Equality.Setoid            as VecSetoid
open import Data.Vec.Relation.Binary.Pointwise.Inductive        as PW
  using (Pointwise)
open import Data.VectorSpace.Core
open import Function            using (_∘_)
open import Level               using (Level)

module Matrix
  {r ℓr : Level}
  {ring : CommutativeRing r ℓr}
  {m′ n′ : ℕ}
  {vsA  : VectorSpace (vecAsModule {ring = ring} (suc n′))}
  {vsB  : VectorSpace (vecAsModule {ring = ring} (suc m′))}
  where

  m n : ℕ
  m = suc m′
  n = suc n′

  open CommutativeRing ring using (setoid; _≈_; _+_; 0#; _*_)
  open VecSetoid     (CommutativeRing.setoid ring) using
    ( _≋_; ≋-isEquivalence; ≋-refl; ≋-sym; ≋-setoid )
  open VecFuncSetoid (CommutativeRing.setoid ring) using (≋-reflexive)
  open import Relation.Binary.Reasoning.Setoid (≋-setoid m)

  module A = VectorSpace vsA
  open A using (A)
  module B = VectorSpace vsB
  open B using () renaming (A to B)
  open VecEq setoid
  open VecEq     A.≈ᴹ-setoid using () renaming (lookup-cong to lookup-cong′)
  open VecSetoid A.≈ᴹ-setoid using () renaming (≋-refl to ≋ᴹ-refl)

  private
    variable
      m′′ : ℕ

  ----------------------------------------------------------------------
  -- Helpers are required for inductive record field functions, because
  -- we can't call them recursively from within their definitions.

  -- Converts matrix into function between vectors.
  g : Vec (Vec A n) (suc m′′) → Vec A n → Vec A (suc m′′)
  g mat v = tabulate ((v A.∙_) ∘ (lookup mat))

  -- `g` is congruent.
  g-cong : ∀ {mat : Vec (Vec A n) (suc m′′)} {u v : Vec A n} →
           u ≋ v → g mat u ≋ g mat v
  g-cong {mat = mat} u≋v =
    tabulate-cong′ (λ k → A.∙-cong u≋v (lookup-cong′ {u = mat} ≋ᴹ-refl k))

  -- `g` is homomorphic under vector addition.
  -- Note: Can't use `B.+ᴹ` or `B.-ᴹ`, because they assume m-length vectors.
  g-homo : ∀ {u v} {mat : Vec (Vec A n) (suc m′′)} →
           g mat (u A.+ᴹ v) ≋ zipWith _+_ (g mat u) (g mat v)
  g-homo {m′′ = zero} = A.∙-distrib-+ʳ Pointwise.∷ Pointwise.[]
  g-homo {m′′ = suc m′′} {mat = mhead ∷ mtail} =
    A.∙-distrib-+ʳ Pointwise.∷ g-homo {mat = mtail}

  g-ε-homo : ∀ {mat : Vec (Vec A n) (suc m′′)} →
             g mat (replicate {n = n} 0#) ≋ replicate {n = (suc m′′)} 0#
  g-ε-homo {m′′ = zero} = A.∙-idˡ Pointwise.∷ Pointwise.[]
  g-ε-homo {m′′ = suc m′′} {mat = mhead ∷ mtail} =
    A.∙-idˡ Pointwise.∷ g-ε-homo {mat = mtail}

  g-⁻¹-homo : ∀ {v} {mat : Vec (Vec A n) (suc m′′)} →
             g mat (A.-ᴹ v) ≋ map B.-_ (g mat v)
  g-⁻¹-homo {m′′ = zero} = A.∙-homo-⁻¹ˡ Pointwise.∷ Pointwise.[]
  g-⁻¹-homo {m′′ = suc m′′} {mat = mhead ∷ mtail} =
    A.∙-homo-⁻¹ˡ Pointwise.∷ g-⁻¹-homo {mat = mtail}

  -- `g` distributes over scalar multiplication.
  g-homo-*ₗ : ∀ {s v} {mat : Vec (Vec A n) (suc m′′)} →
              g mat (s A.*ₗ v) ≋ map (s *_) (g mat v)
  g-homo-*ₗ {m′′ = zero} = A.∙-comm-*ₗʳ Pointwise.∷ Pointwise.[]
  g-homo-*ₗ {m′′ = suc m′′} {mat = mhead ∷ mtail} =
    A.∙-comm-*ₗʳ Pointwise.∷ g-homo-*ₗ {mat = mtail}

  g-homo-*ᵣ : ∀ {s v} {mat : Vec (Vec A n) (suc m′′)} →
              g mat (v A.*ᵣ s) ≋ map (s *_) (g mat v)
  g-homo-*ᵣ {m′′ = zero} = A.∙-comm-*ᵣʳ Pointwise.∷ Pointwise.[]
  g-homo-*ᵣ {m′′ = suc m′′} {mat = mhead ∷ mtail} =
    A.∙-comm-*ᵣʳ Pointwise.∷ g-homo-*ᵣ {mat = mtail}

  ----------------------------------------------------------------------
  -- The meaning of a matrix is a linear mapping between vectors.
  ⟦_⟧ : Vec (Vec A n) m → LinearMap (vecAsModule {ring = ring} n)
                                     (vecAsModule {ring = ring} m)
  ⟦ mat ⟧ = mkLM f homo
    where
    f    = g mat
    homo = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = record
          { isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                { cong = g-cong {mat = mat} }
              ; homo = λ u v → g-homo {mat = mat}
              }
            ; ε-homo = g-ε-homo {mat = mat}
            }
          ; ⁻¹-homo = λ u → g-⁻¹-homo {mat = mat}
          }
        ; *ₗ-homo = λ s xs → g-homo-*ₗ {mat = mat}
        ; *ᵣ-homo = λ s xs → g-homo-*ᵣ {mat = mat}
        }
      }
