import Data.Nat
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

concatSingltons : List (s : List t ** Sorted _ s) -> List t                                         -- промежуточная конструкция

splitSingletons : {rel : t -> t -> Type} -> Sortable t rel =>                                       -- интерфейс
                  (xs  : List t) ->                                                                 -- вход
                  (ss  : List (s : List t ** Sorted rel s) ** Permutation xs (concatSingltons ss))  -- выход

mergeSingletons : {rel : t -> t -> Type} -> Sortable t rel =>                                       -- интерфейс
                  (ss  : List (s : List t ** Sorted rel s)) ->                                      -- вход
                  (xs  : List t ** (Sorted rel xs, Permutation (concatSingltons ss) xs))            -- выход

mergeTwoLists   : {rel : t -> t -> Type} -> Sortable t rel =>                                       -- интерфейс
                  (xs  : List t) -> Sorted rel xs ->                                                -- вход
                  (ys  : List t) -> Sorted rel ys ->                                                -- вход
                  (zs  : List t ** (Sorted rel zs, Permutation (xs ++ ys) zs))                      -- выход

mergeSort       : {rel : t -> t -> Type} -> Sortable t rel =>                                       -- интерфейс
                  (xs  : List t) ->                                                                 -- вход
                  (ys  : List t ** (Sorted rel ys, Permutation xs ys))                              -- выход