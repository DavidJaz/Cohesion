{-# OPTIONS --without-K #-}

module UpperNaturals where

  open import Basics
  open import lib.Basics
  open import lib.NType2

  open import lib.types.Pi
  open import lib.types.Nat
  open import lib.types.Truncation

  ≤-antisymmetry : {n m : ℕ} (_ : n ≤ m) (_ : m ≤ n) → n == m
  ≤-antisymmetry {_} {_} (inl p) _ = p
  ≤-antisymmetry {_} {_} _ (inl p) = ! p
  ≤-antisymmetry {_} {_} (inr p) q = quodlibet (<-to-≱ p q)

  -- A propositional version of _≤_
  _≤p_ : ℕ → ℕ → Prop₀
  n ≤p m = (n ≤ m) , (≤-is-prop {n} {m})

  _is-upward-closed : (N : ℕ → Prop₀) → Type _
  N is-upward-closed = (n m : ℕ) → n ≤ m → (N n) holds → (N m) holds

  upward-closed-is-a-prop : (N : ℕ → Prop₀) → (N is-upward-closed) is-a-prop
  upward-closed-is-a-prop N = mp (λ _ → mp (λ m → mp (λ _ → mp (λ _ → (N m) holds-is-a-prop))))
    where
      mp = mapping-into-prop-is-a-prop

  ℕ→Prop₀-is-a-set : (ℕ → Prop₀) is-a-set
  ℕ→Prop₀-is-a-set = Π-level {_}{_}{ℕ}{λ _ → Prop₀}{0} (λ _ → hProp-is-set _)

  ℕ↑-prop : SubtypeProp (ℕ → Prop₀) _
  ℕ↑-prop = _is-upward-closed , upward-closed-is-a-prop

  {- The Upper Naturals
     An upper natural is an upward closed proposition concerning natural numbers.

     The interpretation is that an upper natural is a natural ``defined by its upper bounds'', in the
     sense that for the proposition N holding of a natural n means that n is an upper bound of N.
     
     The important bit about upper naturals is that they satisfy the well-ordering principle, 
     constructively.
  -}
  ℕ↑ : Type₁
  ℕ↑ = Subtype ℕ↑-prop
   -- Σ (ℕ → Prop₀) _is-upward-closed


  ℕ↑-is-a-set : ℕ↑ is-a-set
  ℕ↑-is-a-set = Subtype-level ℕ↑-prop

  _is-an-upper-bound-of_ : ℕ → ℕ↑ → Type _
  n is-an-upper-bound-of M = ((fst M) n) holds
  
  _≤:↑_ : ℕ↑ → ℕ → Type _
  M ≤:↑ n = n is-an-upper-bound-of M

  ≤:↑-is-a-prop : {M : ℕ↑} {n : ℕ} → (M ≤:↑ n) is-a-prop
  ≤:↑-is-a-prop {M} {n} = ((fst M) n) holds-is-a-prop 

  ≤p-is-upward-closed : {n : ℕ} → (n ≤p_) is-upward-closed
  ≤p-is-upward-closed = λ n m z z₁ → ≤-trans z₁ z

  _^↑ : ℕ → ℕ↑
  n ^↑ = (n ≤p_) , ≤p-is-upward-closed

  -- 0 is bounded above by every number.
  O↑ : ℕ↑
  O↑ = O ^↑

  -- Infinity is defined to be the number with no upper bounds.
  ∞↑ : ℕ↑
  ∞↑ = (λ _ → False) , proof
    where proof : (λ _ → False) is-upward-closed
          proof = λ n m _ z → z

  ∞↑-has-no-upper-bounds : (n : ℕ) → ¬ (∞↑ ≤:↑ n)
  ∞↑-has-no-upper-bounds n = λ z → z
  

  ≤:↑-refl : {n : ℕ} → n is-an-upper-bound-of (n ^↑)
  ≤:↑-refl = ≤-refl

  -- The ordering on the upper naturals is defined by saying that
  -- N is at most M if every upper bound of M is an upper bound of N.
  _≤↑_ : ℕ↑ → ℕ↑ → Type _
  N ≤↑ M = (n : ℕ) → M ≤:↑ n → N ≤:↑ n

  ≤↑-is-a-prop : {N M : ℕ↑} → (N ≤↑ M) is-a-prop
  ≤↑-is-a-prop {N} {M} = mp (λ n → mp (λ _ → ≤:↑-is-a-prop {N} {n}))
    where mp = mapping-into-prop-is-a-prop

  ≤↑-refl : {N : ℕ↑} → N ≤↑ N
  ≤↑-refl = λ n z → z

  ≤↑-trans : {N M P : ℕ↑} → N ≤↑ M → M ≤↑ P → N ≤↑ P
  ≤↑-trans = λ z z₁ n z₂ → z n (z₁ n z₂)
  

  ^↑-is-monotone : {n m : ℕ} → n ≤ m → (n ^↑) ≤↑ (m ^↑)
  ^↑-is-monotone = λ x k x₁ → ≤-trans x x₁

  ^↑-yoneda : {n : ℕ} {M : ℕ↑} → M ≤↑ (n ^↑) → M ≤:↑ n
  ^↑-yoneda {n} {M} = λ x → x n ≤:↑-refl

  ^↑-is-full : {n m : ℕ} → (n ^↑) ≤↑ (m ^↑) → n ≤ m
  ^↑-is-full {n} {m} = λ z → z m (inl idp)

  ^↑-is-ff : {n m : ℕ} → (n ≤ m) ≃ ((n ^↑) ≤↑ (m ^↑))
  ^↑-is-ff {n} {m} = equiv ^↑-is-monotone ^↑-is-full
    (λ b → prop-path (≤↑-is-a-prop {(n ^↑)} {(m ^↑)}) (λ _ → ≤-trans (b m (inl idp))) b)
    (λ a → prop-path ≤-is-prop (≤-trans a (inl idp)) a)

  =-to-≤↑ : {N M : ℕ↑} → N == M → N ≤↑ M
  =-to-≤↑ idp = λ n z → z

  ^↑-is-injective : {n m : ℕ} → (n ^↑) == (m ^↑) → n == m
  ^↑-is-injective {n} {m}  =
    λ x → ≤-antisymmetry (^↑-is-full (=-to-≤↑ x)) (^↑-is-full ((=-to-≤↑ (! x))))

  O↑≤↑ : (N : ℕ↑) → O↑ ≤↑ N
  O↑≤↑ N = λ n x → ^↑-is-monotone (O≤ n) n ≤:↑-refl

  _≤↑∞↑ : (N : ℕ↑) → N ≤↑ ∞↑
  N ≤↑∞↑ = λ n x → quodlibet (∞↑-has-no-upper-bounds n x)


  minℕ : (P : ℕ → Type₀) → ℕ↑
  minℕ P =
    (λ n → min-pred n) ,
      (λ n m x → Trunc-rec (implication n m x))
    where
      min-pred : (n : ℕ) → Prop₀
      min-pred n = ∃ (λ k → (P k) And (k ≤ n))

      implication : (n m : ℕ) (x : n ≤ m)
                    → Σ ℕ (λ k → (P k) And (k ≤ n))
                    → min-pred m holds
      implication n m x = λ {(k , p) → [ k , fst p , ≤-trans (snd p) x ] }

  {- Probably requires propositional resizing
  minℕ↑ : (P : ℕ↑ → Type₀) → ℕ↑
  minℕ↑ P =
    (λ n → min-pred n) ,
      (λ n m x → Trunc-rec (implication n m x))
    where
      min-pred : (n : ℕ) → Prop₀
      min-pred n = ∃ (λ K → (P K) And (K ≤:↑ n))

      implication : (n m : ℕ) (x : n ≤ m)
                    → Σ ℕ↑ (λ K → (P K) And (K ≤:↑ n))
                    → min-pred m holds
      implication n m x = λ {(k , p) → [ k , fst p , ≤-trans (snd p) x ] }
  -}
