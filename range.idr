-- This code defines a predicate for checking whether a number is within a range
-- at the type level.

module Main

import Data.String

-- EqNat

zeroNotSuc : (Z = S k) -> Void
zeroNotSuc Refl impossible

sucNotZero : (S k = Z) -> Void
sucNotZero Refl impossible

noRec : (contra: (j = k) -> Void) -> (S j = S k) -> Void
noRec contra Refl = contra Refl

total checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S j) (S k) = case checkEqNat j k of
                            Yes prf => Yes (cong S prf)
                            No contra => No (noRec contra)

-- IsEven

data IsEven : (n : Nat) -> Type where
    IsEvenZ : IsEven Z
    IsEvenSS : IsEven n -> IsEven (S (S n))

Uninhabited (IsEven (S Z)) where
    uninhabited _ impossible

oneNotEven : (IsEven (S Z)) -> Void
oneNotEven _ impossible

noRecEven : (contra: IsEven n -> Void) -> IsEven (S (S n)) -> Void
noRecEven contra (IsEvenSS prf) = contra prf

sucSucEven : IsEven n -> IsEven (S (S n))
sucSucEven prf = IsEvenSS prf

total checkIsEven : (num : Nat) -> Dec (IsEven num)
checkIsEven Z = Yes IsEvenZ
checkIsEven (S Z) = No absurd
checkIsEven (S (S n)) = case checkIsEven n of
                            Yes prf => Yes (sucSucEven prf)
                            No contra => No (noRecEven contra)

-- IsGreater

data IsGreater : (n : Nat) -> (m : Nat) -> Type where
    IsGreaterZ : IsGreater (S _) Z
    IsGreaterS : IsGreater n m -> IsGreater (S n) (S m)

Uninhabited (IsGreater Z Z) where
    uninhabited _ impossible

Uninhabited (IsGreater Z (S _)) where
    uninhabited _ impossible

noRecGreater : (contra : IsGreater n m -> Void) -> IsGreater (S n) (S m) -> Void
noRecGreater contra (IsGreaterS prf) = contra prf

sucGreater : IsGreater n m -> IsGreater (S n) (S m)
sucGreater prf = IsGreaterS prf

total checkIsGreater : (n : Nat) -> (m : Nat) -> Dec (IsGreater n m)
checkIsGreater Z Z = No absurd
checkIsGreater Z (S _) = No absurd
checkIsGreater (S _) Z = Yes IsGreaterZ
checkIsGreater (S j) (S k) = case checkIsGreater j k of
                                Yes prf => Yes (sucGreater prf)
                                No contra => No (noRecGreater contra)

-- IsLess

data IsLess : (n : Nat) -> (m : Nat) -> Type where
    IsLessInverse : IsGreater n m -> IsLess m n

noLessInverse : (contra : IsGreater n m -> Void) -> IsLess m n -> Void
noLessInverse contra (IsLessInverse prf) = contra prf

total checkIsLess : (n : Nat) -> (m : Nat) -> Dec (IsLess n m)
checkIsLess n m = case checkIsGreater m n of
                    Yes prf => Yes (IsLessInverse prf)
                    No contra => No (noLessInverse contra)

-- IsGreaterEq

data IsGreaterEq : (n : Nat) -> (m : Nat) -> Type where
    IsGreaterEqEZ : IsGreaterEq Z Z
    IsGreaterEqZ : IsGreaterEq (S _) Z
    IsGreaterEqS : IsGreaterEq n m -> IsGreaterEq (S n) (S m)

Uninhabited (IsGreaterEq Z (S _)) where
    uninhabited _ impossible

noRecGreaterEq : (contra : IsGreaterEq n m -> Void) -> IsGreaterEq (S n) (S m) -> Void
noRecGreaterEq contra (IsGreaterEqS prf) = contra prf

sucGreaterEq : IsGreaterEq n m -> IsGreaterEq (S n) (S m)
sucGreaterEq prf = IsGreaterEqS prf

total checkIsGreaterEq : (n : Nat) -> (m : Nat) -> Dec (IsGreaterEq n m)
checkIsGreaterEq Z Z = Yes IsGreaterEqEZ
checkIsGreaterEq Z (S _) = No absurd
checkIsGreaterEq (S _) Z = Yes IsGreaterEqZ
checkIsGreaterEq (S j) (S k) = case checkIsGreaterEq j k of
                                Yes prf => Yes (sucGreaterEq prf)
                                No contra => No (noRecGreaterEq contra)

-- IsLessEq

data IsLessEq : (n : Nat) -> (m : Nat) -> Type where
    IsLessEqInverse : IsGreaterEq n m -> IsLessEq m n

noLessEqInverse : (contra : IsGreaterEq n m -> Void) -> IsLessEq m n -> Void
noLessEqInverse contra (IsLessEqInverse prf) = contra prf

total checkIsLessEq : (n : Nat) -> (m : Nat) -> Dec (IsLessEq n m)
checkIsLessEq n m = case checkIsGreaterEq m n of
                    Yes prf => Yes (IsLessEqInverse prf)
                    No contra => No (noLessEqInverse contra)

-- IsNotEq

data IsNotEq : (n : Nat) -> (m : Nat) -> Type where
    IsNotEqSZ : IsNotEq (S _) Z
    IsNotEqZS : IsNotEq Z (S _)
    IsNotEqS : IsNotEq n m -> IsNotEq (S n) (S m)

Uninhabited (IsNotEq Z Z) where
    uninhabited _ impossible

sucNotEq : IsNotEq n m -> IsNotEq (S n) (S m)
sucNotEq prf = IsNotEqS prf

noRecNotEq : (contra : IsNotEq n m -> Void) -> IsNotEq (S n) (S m) -> Void
noRecNotEq contra (IsNotEqS prf) = contra prf

total checkIsNotEq : (n : Nat) -> (m : Nat) -> Dec (IsNotEq n m)
checkIsNotEq Z Z = No absurd
checkIsNotEq Z (S _) = Yes IsNotEqZS
checkIsNotEq (S _) Z = Yes IsNotEqSZ
checkIsNotEq (S j) (S k) = case checkIsNotEq j k of
                                Yes prf => Yes (sucNotEq prf)
                                No contra => No (noRecNotEq contra)

eqImpliesNotNotEq : n = m -> IsNotEq n m -> Void
eqImpliesNotNotEq Refl {n=Z} _ impossible
eqImpliesNotNotEq Refl {n=(S _)} _ impossible

notEqImpliesNotEq : IsNotEq n m -> n = m -> Void
notEqImpliesNotEq IsNotEqSZ _ impossible
notEqImpliesNotEq IsNotEqZS _ impossible
notEqImpliesNotEq (IsNotEqS prf) Refl = notEqImpliesNotEq prf Refl

-- IsInRange

data IsInRange : (k : Nat) -> (n : Nat) -> (m : Nat) -> Type where
    ItIsInRange : IsGreaterEq k n -> IsLessEq k m -> IsInRange k n m

natTooSmallForRange : (IsGreaterEq k n -> Void) -> IsInRange k n _ -> Void
natTooSmallForRange {k=Z} _ _ impossible
natTooSmallForRange {k=(S _)} _ _ impossible

natTooBigForRange : (IsLessEq k m -> Void) -> IsInRange k _ m -> Void
natTooBigForRange {k=Z} _ _ impossible
natTooBigForRange {k=(S _)} _ _ impossible

total checkIsInRange : (k : Nat) -> (n : Nat) -> (m : Nat) -> Dec (IsInRange k n m)
checkIsInRange k n m = case checkIsGreaterEq k n of
                            Yes prf1 =>
                                case checkIsLessEq k m of
                                    Yes prf2 => Yes (ItIsInRange prf1 prf2)
                                    No contra2 => No (natTooBigForRange contra2)
                            No contra1 => No (natTooSmallForRange contra1)

-- Main function - for testing

readNat : IO Nat
readNat = do
            s <- getLine ;
            case parsePositive s of
                Just i => pure $ fromInteger i
                _ => pure Z

main : IO ()
main = do
        k <- readNat ;
        n <- readNat ;
        m <- readNat ;
        putStrLn $ (show k) ++ " " ++ (show n) ++ " " ++ (show m) ;
        case checkIsInRange k n m of
            Yes prf => putStrLn "yes"
            No contra => putStrLn "no"
