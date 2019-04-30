{-# OPTIONS --without-K #-}

module Bool where
  open import Basics
  open import lib.Basics
  open import lib.types.Bool public

  _≤b_ : Bool → Bool → Prop₀
  true ≤b true = True
  true ≤b false  = False
  false ≤b true = True
  false ≤b false = True

  ≤b-refl : (b : Bool) → (b ≤b b) holds
  ≤b-refl true = unit
  ≤b-refl false = unit

  ≤b-trans : {a b c : Bool} → (a ≤b b) holds → (b ≤b c) holds → (a ≤b c) holds
  ≤b-trans {a} {b} {c} = ≤b-trans' a b c
    where
      ≤b-trans' : (a b c : Bool) → (a ≤b b) holds → (b ≤b c) holds → (a ≤b c) holds
      ≤b-trans' true true true = λ _ _ → unit
      ≤b-trans' true true false = λ _ z → z
      ≤b-trans' true false true = λ _ _ → unit
      ≤b-trans' true false false = λ z _ → z
      ≤b-trans' false true true = λ _ _ → unit
      ≤b-trans' false true false = λ _ _ → unit
      ≤b-trans' false false true = λ _ _ → unit
      ≤b-trans' false false false = λ _ _ → unit

  Bool-to-Prop₀ : Bool → Prop₀
  Bool-to-Prop₀ true = True
  Bool-to-Prop₀ false = False

  Dec-Prop-to-Bool : {i : ULevel} (P : Prop i) → Dec (P holds) → Bool
  Dec-Prop-to-Bool _ (inl _) = true
  Dec-Prop-to-Bool _ (inr _) = false

  Dec-Prop-to-Bool-true-id : {i : ULevel} (P : Prop i) (d : Dec (P holds))
                             → P holds → (Dec-Prop-to-Bool P d) == true
  Dec-Prop-to-Bool-true-id P (inl _) p  = refl
  Dec-Prop-to-Bool-true-id P (inr d) p = quodlibet (d p)

  Dec-Prop-to-Bool-false-id : {i : ULevel} (P : Prop i) (d : Dec (P holds))
                              → ¬ (P holds) → (Dec-Prop-to-Bool P d) == false
  Dec-Prop-to-Bool-false-id P (inl x) np = quodlibet (np x)
  Dec-Prop-to-Bool-false-id P (inr _) np = refl

  _holds-b : Bool → Type₀
  b holds-b = (Bool-to-Prop₀ b) holds
