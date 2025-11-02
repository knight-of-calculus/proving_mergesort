import Data.Nat
import Data.List
import Decidable.Equality
import Control.WellFounded

%default total

interface (DecEq t, LinearOrder t rel) => Sortable t rel where

data ForAll : (prop : t -> Type) -> List t -> Type where
        AllOfEmpty  : ForAll _ []
        AddToAll    : {x : t} -> prop x -> ForAll prop xs -> ForAll prop (x :: xs)

data Sorted : (rel : t -> t -> Type) -> List t -> Type where
        EmptyIsSorted   : Sorted _ []
        ConsToSorted    : {rel : t -> t -> Type} -> Sorted rel xs -> ForAll (rel y) xs -> Sorted rel (y :: xs)

data Permutation : List t -> List t -> Type where
        SameIsPermutation  : Permutation a a
        AddSameHead        : Permutation xs ys -> Permutation (z :: xs) (z :: ys)
        SwapFirstTwo       : Permutation (x :: y :: zs) (y :: x :: zs)
        TransitivePerm     : {xs, ys, zs : List t} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs

proofPermAddAssociative : {xs, ys, zs : List t} -> Permutation (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
proofPermAdd : {as, bs, cs, ds : List t} -> Permutation as bs -> Permutation cs ds -> Permutation (as ++ cs) (bs ++ ds)

mergeTwoLists : {rel : t -> t -> Type} -> Sortable t rel =>
                (xs  : List t) -> Sorted rel xs ->
                (ys  : List t) -> Sorted rel ys ->
                (zs  : List t ** (Sorted rel zs, Permutation (xs ++ ys) zs))

concatSingltons : List (s : List t ** Sorted _ s) -> List t
concatSingltons [] = []
concatSingltons ((s ** _) :: st) = s ++ concatSingltons st

-- рассмотрим случай, когда из-за нестрогой спецификации синглтонов (как списков произвольной длины, а не списков строго длины = 1),
-- у нас не получается показать тотальность mergeSingletons в силу того, что не происходит явного структурного уменьшения
-- аргумента рекурсивного вызова;
-- в реализации ниже мы не следуем изначальному плану:
--      mergeSingletons (sx :: sy :: st) = mergeTwoLists (mergeTwoLists sx sy) (mergeSingletons st),
-- а делаем немного по-другому, сокращая один вызов mergeTwoLists.
-- так эффективнее и это работает правильно (мы не нарушаем результирующую спецификацию), однако возможно это именно из-за
-- "размывания" понятия синглтона: по факту у нас на его месте может оказаться список неединичной длины.
-- в таком случае мы можем показать тотальность с помощью техники определения доступности термов (по длине доказательства)

mergeSingletonsWellFounded : {rel : t -> t -> Type} -> Sortable t rel =>
                             (ss  : List (s : List t ** Sorted rel s)) ->
                             {0 acc : SizeAccessible ss } ->
                             (ys  : List t ** (Sorted rel ys, Permutation (concatSingltons ss) ys))
mergeSingletonsWellFounded [] = ([] ** (EmptyIsSorted, SameIsPermutation))
mergeSingletonsWellFounded [(s ** s_sorted)] = (s ** (s_sorted, rewrite appendNilRightNeutral s in SameIsPermutation))
mergeSingletonsWellFounded ((sx ** sx_sorted) :: (sy ** sy_sorted) :: st) {acc = (Access rec)} =
        let
        (merged_xy ** (merged_xy_sorted, merged_xy_perm)) = mergeTwoLists sx sx_sorted sy sy_sorted
        (ys ** (ys_sorted, ss_perm)) =
                mergeSingletonsWellFounded ((merged_xy ** merged_xy_sorted) :: st)
                                           {acc = (rec ((merged_xy ** merged_xy_sorted) :: st) reflexive)}
        ys_perm = TransitivePerm
                        (proofPermAddAssociative {xs = sx} {ys = sy} {zs = concatSingltons st})
                        (TransitivePerm
                                (proofPermAdd merged_xy_perm SameIsPermutation)
                                (TransitivePerm SameIsPermutation ss_perm))
        in
        (ys ** (ys_sorted, ys_perm))

mergeSingletons : {rel : t -> t -> Type} -> Sortable t rel =>
                  (ss  : List (s : List t ** Sorted rel s)) ->
                  (xs  : List t ** (Sorted rel xs, Permutation (concatSingltons ss) xs))
mergeSingletons ss = mergeSingletonsWellFounded ss {acc = sizeAccessible ss}

splitSingletons : {rel : t -> t -> Type} -> Sortable t rel => (xs  : List t) ->
                  (ss  : List (s : List t ** Sorted rel s) ** Permutation xs (concatSingltons ss))

mergeSort : {rel : t -> t -> Type} -> Sortable t rel => (xs  : List t) -> (ys  : List t ** (Sorted rel ys, Permutation xs ys))