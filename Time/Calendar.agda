-- The proleptic Gregorian calendar with astronomical year numbering,
-- used by ISO 8601
module Time.Calendar where

open import Math.Dec
open import Math.Mod
open import Math.Int using (ℤ; ℤ-IsSet)
open import Math.Nat
open import Math.Type

infix 4 _∣_

-- divides
-- TODO: move this?
_∣_ : ℕ → ℤ → Set
d ∣ n = fromℤ {d = d} n ≡ fromℕ {d = d} 0

∣-IsProp : ∀ {d n} → IsProp (d ∣ n)
∣-IsProp {d = d} = Mod-IsSet {d = d} _ _

∣-Dec : ∀ d n → Dec (d ∣ n)
∣-Dec d n = Mod-HasDecEq {d = d} _ _

-- years

Year : Type
Year = ℤ

Year-IsSet : IsSet Year
Year-IsSet = ℤ-IsSet

IsLeapYear : Year → Type
IsLeapYear y = ((4 ∣ y) ∧ (¬ (100 ∣ y))) ∨ (400 ∣ y)

IsLeapYear-IsProp : ∀ {y} → IsProp (IsLeapYear y)
IsLeapYear-IsProp = ∨-IsProp

IsLeapYear-Dec : ∀ y → Dec (IsLeapYear y)
IsLeapYear-Dec y = ∨-Dec (∧-Dec (∣-Dec 4 y) (¬-Dec (∣-Dec 100 y))) (∣-Dec 400 y)

-- months

MonthOfYear : Type
MonthOfYear = Σ[ n ∈ ℕ ] (1 ≤ n) × (n ≤ 12)

Month : Type
Month = Year × MonthOfYear

-- days

numDays : Month → ℕ
numDays (y , ( 1 , _)) = 31
numDays (y , ( 2 , _)) = case IsLeapYear-Dec y of λ { (yes _) → 29 ; (no _) → 28 }
numDays (y , ( 3 , _)) = 31
numDays (y , ( 4 , _)) = 30
numDays (y , ( 5 , _)) = 31
numDays (y , ( 6 , _)) = 30
numDays (y , ( 7 , _)) = 31
numDays (y , ( 8 , _)) = 31
numDays (y , ( 9 , _)) = 30
numDays (y , (10 , _)) = 31
numDays (y , (11 , _)) = 30
numDays (y , (12 , _)) = 31
numDays (y , (zero , 1≤m , m≤12)) = ⊥-rec (¬-<-zero 1≤m)
numDays (y , (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))))) , 1≤m , m≤12)) =
  ⊥-rec (¬-<-zero (<-k+-inv m≤12))

DayOfMonth : Month → Type
DayOfMonth m = Σ[ n ∈ ℕ ] (1 ≤ n) × (n ≤ numDays m)

Day : Type
Day = Σ[ m ∈ Month ] DayOfMonth m
