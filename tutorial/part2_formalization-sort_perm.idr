import Data.Nat

%default total

-- 3. свойство, выражающее истинность некоторого высказывания относительно всех элементов списка
data ForAll : (prop : t -> Type) -> List t -> Type where
        AllOfEmpty  : ForAll _ []
        AddToAll    : {x : t} -> prop x -> ForAll prop xs -> ForAll prop (x :: xs)

-- 2. базовые утверждения об упорядоченности
data Sorted : (rel : t -> t -> Type) -> List t -> Type where
        EmptyIsSorted   : Sorted _ []
        ConsToSorted    : {rel : t -> t -> Type} -> Sorted rel xs -> ForAll (rel y) xs -> Sorted rel (y :: xs)

-- 1. базовые утверждения о перестановках
data Permutation : List t -> List t -> Type where
        SameIsPermutation  : Permutation a a
        AddSameHead        : Permutation xs ys -> Permutation (z :: xs) (z :: ys)
        SwapFirstTwo       : Permutation (x :: y :: zs) (y :: x :: zs)
        TransitivePerm     : {xs, ys, zs : List t} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs

-- определить базовый набор свойств, или аксиом для формальной спецификации -- это искусство!
-- их должно быть достаточно, чтобы доказывать требуемые инварианты, но не более того. например:
--      SingletonIsSorted : Sorted _ [_]        <== создаст проблемы из-за избыточности в паттерн-матчинге!
--      EmptyPermutes     : Permutation [] []   <== избыточно вместе с SameIsPermutation
--      SingletonPermutes : Permutation [x] [x] <== избыточно, также частный случай Permutation a a

-- 4. примеры доказательств
proofPerm_1 : Permutation [1, 2, 3] [2, 1, 3]
proofPerm_1 = SwapFirstTwo

proofPerm_2 : Permutation [1, 2, 3] [1, 3, 2]
proofPerm_2 = AddSameHead SwapFirstTwo

proofPerm_3 : Permutation [3, 1, 2] [2, 3, 1]
proofPerm_3 = TransitivePerm (AddSameHead SwapFirstTwo) SwapFirstTwo
{-
        TransitivePerm                  -- 4. по транзитивности получаем требуемую перестановку * <=> ***
                (
                        AddSameHead     -- 2. добавляем общую голову к перестановке:   *[3, 1, 2] <=> [3, 2, 1]**
                        SwapFirstTwo    -- 1. в хвосте [3, 1, 2] = [1, 2] перестановка:    [1, 2] <=>    [2, 1]
                )
                SwapFirstTwo            -- 3. меняем первые два в **: [3, 2, 1] <=> [2, 3, 1]***
-}

proofSorted : Sorted LTE [1, 2, 3]      -- индуктивный тип LTE имеет два конструктора: LTESucc и LTEZero
proofSorted =   let                             -- LTEZero утверждает, что ∀ n: Nat верно 0 <= n, 
                                                -- LTESucc утверждает, что ∀ n, m: Nat верно (n <= m) --> (n + 1 <= m + 1)

                lte_1_2 : LTE 1 2                       -- показываем, что 1 <= 2:
                lte_1_2 = LTESucc LTEZero               --      0 <= 1 --> 1 <= 2

                lte_1_3 : LTE 1 3                       -- показываем, что 1 <= 3:
                lte_1_3 = LTESucc LTEZero               --      0 <= 2 --> 1 <= 3

                lte_2_3 : LTE 2 3                       -- показываем, что 2 <= 3:
                lte_2_3 = LTESucc (LTESucc LTEZero)     --      0 <= 1 --> 1 <= 2 --> 2 <= 3

                single_3 : List Nat
                single_3 = [3]

                sorted_3 : Sorted LTE single_3          -- 1. начинаем с синглтона [3] из последнего элемента, он отсортирован
                sorted_3 = ConsToSorted EmptyIsSorted AllOfEmpty      -- (или по лемме proofSingletonIsSorted)

                forall_2_3 : ForAll (LTE 2) single_3    -- 2. доказываем, что 2 <= всем элементам этого синглтона [3]
                forall_2_3 = AddToAll lte_2_3 AllOfEmpty

                sorted_23 : Sorted LTE [2, 3]           -- 3. доказываем, что список [2, 3] отсортирован
                sorted_23 = ConsToSorted sorted_3 forall_2_3

                forall_1_2 : ForAll (LTE 1) [2]
                forall_1_2 = AddToAll (LTESucc LTEZero) AllOfEmpty

                forall_1_3 : ForAll (LTE 1) single_3
                forall_1_3 = AddToAll (LTESucc LTEZero) AllOfEmpty

                forall_1_23 : ForAll (LTE 1) [2, 3]     -- 4. доказываем, что 1 <= всем элементам в [2, 3]
                forall_1_23 = AddToAll lte_1_2 (AddToAll lte_1_3 AllOfEmpty)
                                {- альтернативный вариант с использованием леммы proofForAllAdd:
                                        proofForAllAdd forall_1_2 forall_1_3
                                                where
                                                forall_1_2 : ForAll (LTE 1) [2]
                                                forall_1_2 = AddToAll (LTESucc LTEZero) AllOfEmpty

                                                forall_1_3 : ForAll (LTE 1) single_3
                                                forall_1_3 = AddToAll (LTESucc LTEZero) AllOfEmpty
                                -}
                in ConsToSorted sorted_23 forall_1_23   -- 5. доказываем, что список [1, 2, 3] отсортирован

-- c помощью зависимых типов первого класса можно выражать и доказывать сколь угодно сложные свойства!
proofSingletonIsSorted : {rel : t -> t -> Type} -> Sorted rel [_]
proofSingletonIsSorted = ConsToSorted EmptyIsSorted AllOfEmpty

proofForAllAdd : ForAll p xs -> ForAll p ys -> ForAll p (xs ++ ys)
proofForAllAdd AllOfEmpty p_ys = p_ys
proofForAllAdd (AddToAll p_x all_xs) all_ys = AddToAll p_x (proofForAllAdd all_xs all_ys)

proofPermAddAssociative : {xs, ys, zs : List t} -> Permutation (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
proofPermAddAssociative {xs = []} = SameIsPermutation
proofPermAddAssociative {xs = (x :: xt)} = AddSameHead (proofPermAddAssociative {xs = xt})