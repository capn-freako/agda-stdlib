------------------------------------------------------------------------
-- The Agda standard library
--
-- A denotation for `Data.Vec` using `Data.VectorSpace`.
------------------------------------------------------------------------

-- {-# OPTIONS --without-K --safe #-}
{-# OPTIONS --safe #-}

open import Algebra               using (CommutativeRing)
open import Algebra.Module        using (Module)
open import Level                 using (Level; _⊔_)  -- ; suc)
open import Data.VectorSpace.Core

module Data.Vec.Denotation
  {r ℓr v ℓv : Level}
  {ring      : CommutativeRing r ℓr}
  {mod       : Module ring v ℓv}
  (vs        : VectorSpace mod)
  where

open import Agda.Builtin.Sigma  using (_,_; fst; snd)
open import Algebra.Definitions
open import Algebra.Module.Morphism.Bundles
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base       hiding (_⊔_; _+_; _*_)
open import Data.Vec.Base
open import Data.Vec.Properties using (zipWith-assoc)
import      Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecFuncSetoid
import      Data.Vec.Relation.Binary.Equality.Setoid            as VecSetoid
open import Data.Vec.Relation.Binary.Pointwise.Inductive        as PW
  using (Pointwise)
open import Function            using (_∘_; flip; _$_)
open import Relation.Binary     using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as EQ
  -- using (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
  using (_≗_)
open import Relation.Binary.Reasoning.MultiSetoid
open VectorSpace vs
  using ( setoid; A; sym; refl
        ; _+_ ; +-assoc; +-comm; +-cong ; +-identity
        ; _*_ ; *-assoc; *-comm; *-cong ; *-identity; *-identityˡ; *-identityʳ
        ; _≈_; _≈ᴹ_
        ; -_; -‿cong; -‿inverse
        ; 0#; zeroˡ; zeroʳ; distribʳ; distribˡ
        )
open VecSetoid     setoid using ( ≋-isEquivalence; ≋-refl; _≋_; ≋-sym )
                                -- ; ≋-setoid; ≋-sym; ≋-trans)
open VecFuncSetoid setoid using (≋-reflexive)

private
  variable
    -- a b : Level
    -- A   : Set a
    -- B   : Set b
    m n : ℕ

-- `Vec` as `Module`, to support `LinearMap`.
-- (See `Algebra.Module.Morphism.Bundles.LinearMap`.)
-- record VecMod {n} : Set r where
--   constructor mk
--   field
--     vec : Vec S n

-- instance
--   -- vecMod : Module ring v ℓv
--   vecMod : Module ring v ℓv VecMod
--   vecMod = {!!}

-- instance
  -- vecMod : Module ring v ℓv -- Where is ring coming from?

-- record VecAsModule : Set ? where
--   constructor mk
--   field
--     vecMod : Module ring v ℓv

-- vecAsModule : (n : ℕ) → VecAsModule
-- vecAsModule : (n : ℕ) → Module ring v ℓv
-- vecAsModule : (n : ℕ) → Module ring r ℓv

-- ∷-++ : ∀ {x x₁ n} → (xs : Vec A n) → x ∷ x₁ ∷ xs ≋ x ∷ [ x₁ ] ++ xs
-- ∷-++ {x} {x₁} []       = ≋-refl
-- ∷-++ {x} {x₁} (x₂ ∷ xs) = {!!}

∷-cong₂ : ∀ {n} {x y} {xs ys : Vec A n} → x ≈ y → xs ≋ ys → x ∷ xs ≋ y ∷ ys
∷-cong₂ {xs = []} {ys = []} x≈y _                     = x≈y PW.∷ PW.[]
∷-cong₂ {xs = x₁ ∷ []} {ys = y₁ ∷ []} x≈y xs≈ys        =
  x≈y PW.∷ (PW.head xs≈ys) PW.∷ PW.[]
∷-cong₂ {n} {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} x≈y x₁∷xs≋y₁∷ys =
  PW.++⁺ x∷[x₁]≋y∷[y₁] xs≋ys
  where
  x₁≈y₁  = PW.head x₁∷xs≋y₁∷ys
  xs≋ys = PW.tail x₁∷xs≋y₁∷ys
  x∷[x₁]≋y∷[y₁] = ∷-cong₂ {xs = [ x₁ ]} {ys = [ y₁ ]} x≈y
                         ( ∷-cong₂ {x = x₁} {y = y₁} {xs = []} {ys = []}
                                   x₁≈y₁ ≋-refl
                         )
  
module _ {f : A → A} where

  map-cong₁ : Congruent₁ _≈_ f → Congruent₁ (_≋_{n})  (map f)
  map-cong₁ f-cong {[]}     {[]}     xs≋ys = xs≋ys
  map-cong₁ f-cong {x ∷ xs} {y ∷ ys} xs≋ys =
    ∷-cong₂ (f-cong (PW.head xs≋ys)) (map-cong₁ f-cong (PW.tail xs≋ys))
  
module _ {f : A → A → A} where

  zipWith-cong₂ : Congruent₂ _≈_ f → Congruent₂ (_≋_ {n}) (zipWith f)
  zipWith-cong₂ f-cong₂ {[]} {[]} {[]} {[]} _   _   = ≋-refl
  zipWith-cong₂ f-cong₂ {x ∷ xs} {y ∷ ys} {u ∷ us} {v ∷ vs}
                x∷xs≋y∷ys u∷us≋v∷vs = ∷-cong₂ (f-cong₂ x≈y u≈v) (zipWith-cong₂ f-cong₂ xs≋ys us≋vs)
    where
    x≈y   = PW.head x∷xs≋y∷ys
    xs≋ys = PW.tail x∷xs≋y∷ys
    u≈v   = PW.head u∷us≋v∷vs
    us≋vs = PW.tail u∷us≋v∷vs
  
  zipWith-assoc′ : Associative _≈_ f → Associative _≋_ (zipWith {n = n} f)
  zipWith-assoc′ assoc []       []       []       = ≋-refl
  zipWith-assoc′ assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    ∷-cong₂ (assoc x y z) (zipWith-assoc′ assoc xs ys zs)

  zipWith-comm : ∀ {n} → Commutative _≈_ f → Commutative (_≋_ {n}) (zipWith f)
  zipWith-comm f-comm =
    λ { []       []       → ≋-refl
      ; (x ∷ xs) (y ∷ ys) → ∷-cong₂ (f-comm x y) (zipWith-comm f-comm xs ys) }

  map-cong : ∀ {x y : A} {xs ys : Vec A n} → Congruent₂ _≈_ f →
             x ≈ y → xs ≋ ys → map (f x) xs ≋ map (f y) ys
  map-cong {.zero}      {x} {y} {[]}      {[]}     f-cong x≈y xs≋ys = ≋-refl
  map-cong {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} f-cong x≈y xs≋ys =
    ∷-cong₂ (f-cong x≈y (PW.head xs≋ys)) (map-cong f-cong x≈y (PW.tail xs≋ys))

  map-assoc : ∀ {x y} {xs : Vec A n} → Associative _≈_ f →
              map (f (f x y)) xs ≋ map (f x) (map (f y) xs)
  map-assoc {.zero}      {x} {y} {[]}     f-assoc = ≋-refl
  map-assoc {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc =
    ∷-cong₂ (f-assoc x y x₁) (map-assoc f-assoc)

  assoc′ : ∀ {x y z} →
           Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
           f y (f x z) ≈ f (f x y) z
  assoc′ {x} {y} {z} f-assoc f-comm f-cong = begin⟨ setoid ⟩
    f y (f x z) ≈⟨ sym (f-assoc y x z) ⟩
    f (f y x) z ≈⟨ f-cong (f-comm y x) refl ⟩
    f (f x y) z ∎
           
  assoc′′ : ∀ {x y z} →
           Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
           f y (f x z) ≈ f x (f y z)
  assoc′′ {x} {y} {z} f-assoc f-comm f-cong = begin⟨ setoid ⟩
    f y (f x z) ≈⟨ assoc′ f-assoc f-comm f-cong ⟩
    f (f x y) z ≈⟨ f-assoc x y z ⟩
    f x (f y z) ∎
           
  map-assoc′ : ∀ {x y} {xs : Vec A n} →
              Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
              map (f y) (map (f x) xs) ≋ map (f  (f x y)) xs
  map-assoc′ {.zero}      {x} {y} {[]}     f-assoc f-comm f-cong = ≋-refl
  map-assoc′ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc f-comm f-cong =
    ∷-cong₂ (assoc′ f-assoc f-comm f-cong) (map-assoc′ f-assoc f-comm f-cong)
  
  map-assoc′′ : ∀ {x y} {xs : Vec A n} →
              Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
              map (f y) (map (f x) xs) ≋ map (f x) (map (f y) xs)
  map-assoc′′ {.zero}      {x} {y} {[]}     f-assoc f-comm f-cong = ≋-refl
  map-assoc′′ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc f-comm f-cong =
    ∷-cong₂ (assoc′′ f-assoc f-comm f-cong) (map-assoc′′ f-assoc f-comm f-cong)
  
module _ {f : A → A → A} {ε : A} where

  zipWith-idˡ : ∀ {n} → LeftIdentity _≈_ ε f →
               LeftIdentity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-idˡ ≈-idˡ = λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (≈-idˡ x) (zipWith-idˡ ≈-idˡ xs) }

  zipWith-idʳ : ∀ {n} → RightIdentity _≈_ ε f →
               RightIdentity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-idʳ ≈-idʳ = λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (≈-idʳ x) (zipWith-idʳ ≈-idʳ xs) }

  zipWith-id : ∀ {n} → Identity _≈_ ε f →
               Identity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-id ≈-id = zipWith-idˡ (fst ≈-id) , zipWith-idʳ (snd ≈-id)

  map-zeroˡ : {xs : Vec A n} → LeftZero _≈_ ε f →
             map (f ε) xs ≋ replicate ε
  map-zeroˡ {.zero}      {[]}     f-zeroˡ = ≋-refl
  map-zeroˡ {.(ℕ.suc _)} {x ∷ xs} f-zeroˡ = ∷-cong₂ (f-zeroˡ x) (map-zeroˡ f-zeroˡ)
  
  map-zeroʳ : {x : A} → RightZero _≈_ ε f →
             map (f x) (replicate {n = n} ε) ≋ replicate ε
  map-zeroʳ {zero}        f-zeroʳ = ≋-refl
  map-zeroʳ {ℕ.suc n} {x} f-zeroʳ = ∷-cong₂ (f-zeroʳ x) (map-zeroʳ f-zeroʳ)
  
  map-identity : {xs : Vec A n} → LeftIdentity _≈_ ε f →
             map (f ε) xs ≋ xs
  map-identity {.zero}      {[]}     f-identity = ≋-refl
  map-identity {.(ℕ.suc _)} {x ∷ xs} f-identity = ∷-cong₂ (f-identity x) (map-identity f-identity)
  
module _ {_⊕_ : A → A → A} {_⊛_ : A → A → A} where

  map-distribʳ : ∀ {x y} {xs : Vec A n} → (_DistributesOverʳ_ _≈_) _⊛_ _⊕_ →
                map ((x ⊕ y) ⊛_) xs ≋ zipWith _⊕_ (map (x ⊛_) xs) (map (y ⊛_) xs)
  map-distribʳ {.zero}      {x} {y} {[]}     ⊛-distrib-⊕ = ≋-refl
  map-distribʳ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} ⊛-distrib-⊕ =
    ∷-cong₂ (⊛-distrib-⊕ x₁ x y) (map-distribʳ ⊛-distrib-⊕)

  map-distribˡ : ∀ {x} {xs ys : Vec A n} → (_DistributesOverˡ_ _≈_) _⊛_ _⊕_ →
                map (x ⊛_) (zipWith _⊕_ xs ys) ≋ zipWith _⊕_ (map (x ⊛_) xs)
                                                             (map (x ⊛_) ys)
  map-distribˡ {.zero}      {x} {[]}     {[]}     ⊛-distrib-⊕ = ≋-refl
  map-distribˡ {.(ℕ.suc _)} {x} {x₁ ∷ xs} {y ∷ ys} ⊛-distrib-⊕ =
    ∷-cong₂ (⊛-distrib-⊕ x x₁ y) (map-distribˡ ⊛-distrib-⊕)

module _ {_⊕_ : A → A → A} {⊝_ : A → A} {ε : A} where

  zipWith-inverseˡ : {xs : Vec A n} → LeftInverse _≈_ ε ⊝_ _⊕_ →
                    zipWith _⊕_ (map ⊝_ xs) xs ≋ replicate {n = n} ε
  zipWith-inverseˡ {.zero}      {[]}     ≈-inv = ≋-refl
  zipWith-inverseˡ {.(ℕ.suc _)} {x ∷ xs} ≈-inv =
    ∷-cong₂ (≈-inv x) (zipWith-inverseˡ ≈-inv)
                    
  zipWith-inverseʳ : {xs : Vec A n} → RightInverse _≈_ ε ⊝_ _⊕_ →
                    zipWith _⊕_ xs (map ⊝_ xs) ≋ replicate {n = n} ε
  zipWith-inverseʳ {.zero}      {[]}     ≈-inv = ≋-refl
  zipWith-inverseʳ {.(ℕ.suc _)} {x ∷ xs} ≈-inv =
    ∷-cong₂ (≈-inv x) (zipWith-inverseʳ ≈-inv)
                    
  map-inverse : Inverse _≈_ ε ⊝_ _⊕_ →
                Inverse (_≋_ {n}) (replicate ε) (map ⊝_) (zipWith _⊕_)
  map-inverse {zero}    ≈-inv = (λ { [] → ≋-refl })
                              , (λ { [] → ≋-refl })
  map-inverse {ℕ.suc n} (≈-invˡ , ≈-invʳ) =
    (λ { (x ∷ xs) → ∷-cong₂ (≈-invˡ x) (zipWith-inverseˡ ≈-invˡ) })
    , λ { (x ∷ xs) → ∷-cong₂ (≈-invʳ x) (zipWith-inverseʳ ≈-invʳ) }
  
*-assoc′ : ∀ {x y z} → x * y * z ≈ y * (x * z)
*-assoc′ {x} {y} {z} = begin⟨ setoid ⟩
  x * y * z   ≈⟨ *-cong (*-comm x y) refl ⟩
  y * x * z   ≈⟨ *-assoc y x z ⟩
  y * (x * z) ∎

*-assoc′′ : ∀ {x y z} → x * (y * z) ≈ y * x * z
*-assoc′′ {x} {y} {z} = begin⟨ setoid ⟩
  x * (y * z) ≈⟨ sym (*-assoc x y z) ⟩
  x * y * z   ≈⟨ *-cong (*-comm x y) refl ⟩
  y * x * z   ∎

*-assoc′′′ : ∀ {x y z} → x * (y * z) ≈ y * (x * z)
*-assoc′′′ {x} {y} {z} = begin⟨ setoid ⟩
  x * (y * z) ≈⟨ sym (*-assoc x y z) ⟩
  x * y * z   ≈⟨ *-cong (*-comm x y) refl ⟩
  y * x * z   ≈⟨ *-assoc y x z ⟩
  y * (x * z) ∎

vecAsModule : (n : ℕ) → Module ring r (r ⊔ ℓr)
vecAsModule n = record
  { Carrierᴹ = Vec A n
  ; _≈ᴹ_     = _≋_
  ; _+ᴹ_     = zipWith _+_
  ; _*ₗ_     = λ x v → map (x *_) v
  ; _*ᵣ_     = λ v x → map (x *_) v
  ; 0ᴹ       = replicate 0#
  ; -ᴹ_      = map (-_)
  ; isModule = record
      { isBimodule = record
          { isBisemimodule = record
              { +ᴹ-isCommutativeMonoid = record
                  { isMonoid = record
                      { isSemigroup = record
                          { isMagma = record
                              { isEquivalence = ≋-isEquivalence n
                              ; ∙-cong        = zipWith-cong₂ +-cong
                              }
                          ; assoc   = zipWith-assoc′ +-assoc
                          }
                      ; identity    = zipWith-id +-identity
                      }
                  ; comm     = zipWith-comm +-comm
                  }
              ; isPreleftSemimodule = record
                  { *ₗ-cong      =
                      λ { {x} {y} {[]}     {[]}     x≈y u≋v → ≋-refl
                        ; {x} {y} {u ∷ us} {v ∷ vs} x≈y u≋v →
                            ∷-cong₂ (*-cong x≈y (PW.head u≋v))
                                    (map-cong *-cong x≈y (PW.tail u≋v))
                        }
                  ; *ₗ-zeroˡ     =
                      λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (zeroˡ x) (map-zeroˡ {f = _*_} zeroˡ)
                        }
                  ; *ₗ-distribʳ  =
                      λ { []       _ _ → ≋-refl
                        ; (x₁ ∷ xs) x y →
                            ∷-cong₂ (distribʳ x₁ x y) (map-distribʳ distribʳ)
                        }
                  ; *ₗ-identityˡ =
                      λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (*-identityˡ x)
                                             (map-identity {f = _*_} *-identityˡ)
                        }
                  ; *ₗ-assoc     =
                      λ { x y xs → map-assoc {x = x} {y = y} {xs = xs} *-assoc }
                  ; *ₗ-zeroʳ     = λ x → map-zeroʳ {x = x} zeroʳ
                  ; *ₗ-distribˡ  =
                      λ { x []       []       → ≋-refl
                        ; x (u ∷ us) (v ∷ vs) → ∷-cong₂ (distribˡ x u v)
                                                        (map-distribˡ distribˡ)
                        }
                  }
              ; isPrerightSemimodule = record
                  { *ᵣ-cong      =
                      λ { {[]}      {[]}     {x} {y} xs≋ys x≈y → ≋-refl
                        ; {x₁ ∷ xs} {y₁ ∷ ys} {x} {y} xs≋ys x≈y →
                            ∷-cong₂ (*-cong x≈y (PW.head xs≋ys))
                                    (map-cong *-cong x≈y (PW.tail xs≋ys))
                        }
                  ; *ᵣ-zeroʳ     =
                      λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (zeroˡ x) (map-zeroˡ {f = _*_} zeroˡ)
                        }
                  ; *ᵣ-distribˡ  =
                      λ { []       x y → ≋-refl
                        ; (x₁ ∷ xs) x y →
                            ∷-cong₂ (distribʳ x₁ x y) (map-distribʳ distribʳ)
                        }
                  ; *ᵣ-identityʳ =
                      λ { []       → ≋-refl
                        ; (x ∷ xs) →
                            ∷-cong₂ (*-identityˡ x)
                                    (map-identity {f = _*_} *-identityˡ)
                        }
                  ; *ᵣ-assoc     =
                      λ { []       x y → ≋-refl
                        ; (x₁ ∷ xs) x y →
                            ∷-cong₂ *-assoc′′
                                    (map-assoc′ *-assoc *-comm *-cong)
                        }
                  ; *ᵣ-zeroˡ     = λ { x → map-zeroʳ {f = _*_} zeroʳ }
                  ; *ᵣ-distribʳ  =
                      λ { x []        []       → ≋-refl
                        ; x (x₁ ∷ xs) (y₁ ∷ ys) →
                            ∷-cong₂ (distribˡ x x₁ y₁) (map-distribˡ distribˡ)
                        }
                  }
              ; *ₗ-*ᵣ-assoc          =
                  λ { _ []       y → ≋-refl
                    ; _ (_ ∷ _) y →
                        ∷-cong₂ *-assoc′′′ (map-assoc′′ *-assoc *-comm *-cong)
                    }
              }
          ; -ᴹ‿cong = map-cong₁ -‿cong
          ; -ᴹ‿inverse = map-inverse -‿inverse
          }
      }
  }

------------------------------------------------------------------------
-- The meaning of a matrix is a linear mapping between vectors.

module _ (vsFrom : VectorSpace (vecAsModule n)) where

  open VectorSpace vsFrom using (_∙_; ∙-congʳ; ∙-congˡ; setoid)
  open VecSetoid   setoid using ( ≋-isEquivalence; ≋-refl; _≋_; ≋-sym )

  -- ≋⇒≗ : {xs ys : Vec A n} {mat : Vec (Vec A n) m} →
  --       xs ≋ ys → ((xs ∙_) ∘ (lookup mat)) ≗ ((ys ∙_) ∘ (lookup mat))
  -- ≋⇒≗ {xs = []}     {ys = []}     xs≋ys = λ _ → EQ.refl
  -- ≋⇒≗ {xs = x ∷ xs} {ys = y ∷ ys} xs≋ys = {!!}

  -- lookup-cong : ∀ {n} → {v : Vec A n} → (k : Fin n) →
  --               lookup v k ≈ lookup v k
  -- lookup-cong              zero    = refl
  -- lookup-cong {v = _ ∷ xs} (suc k) = lookup-cong {v = xs} k
  
  -- lookup-cong : ∀ {b ℓb m n} → {B : Set b} → {u : Vec B m} {v : Vec B n} →
  lookup-cong : ∀ {b ℓb m n} → {B : Set _} → {u : Vec B m} {v : Vec B n} →
                {_~_ : Rel B ℓb} ⦃ _ : IsEquivalence _~_ ⦄ →
                u ≋ v → (k : Fin n) → lookup u k ~ lookup v k
  lookup-cong              zero    = IsEquivalence.refl _
  lookup-cong {v = _ ∷ xs} (suc k) = lookup-cong {v = xs} k
  
  ∙-∘-lookup-cong : {xs ys : Vec A n} {mat : Vec (Vec A n) m} →
                    xs ≋ ys → ∀ k →
                    (xs ∙ (lookup mat k)) ≈ (ys ∙ (lookup mat k))
  ∙-∘-lookup-cong {xs = []}     {ys = []}     xs≋ys k =
    ∙-congˡ {!lookup-cong!}  -- Goal: lookup mat k ≋ lookup mat k
  ∙-∘-lookup-cong {xs = x ∷ xs} {ys = y ∷ ys} xs≋ys k = {!!}

  ⟦_⟧ : Vec (Vec A n) m → LinearMap (vecAsModule n) (vecAsModule m)
  ⟦ mat ⟧ = mkLM f homo
    where
    f    = tabulate ∘ flip (_∙_ ∘ lookup mat)
    homo = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = record
          { isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                { cong = λ { {[]}     {[]}     xs≋ys → {!!}
                           ; {x ∷ xs} {y ∷ ys} xs≋ys → {!!} }
                    -- λ { {[]}     {[]} xs≋ys     → ≋-refl
                    --   ; {x ∷ xs} {y ∷ ys} xs≋ys →
                    --       {!!}
                    --   }
                }
              ; homo = {!!}
              }
            ; ε-homo = {!!}
            }
          ; ⁻¹-homo = {!!}
          }
        ; *ₗ-homo = {!!}
        ; *ᵣ-homo = {!!}
        }
      }
