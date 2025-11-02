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

proofForAllTransitive : {rel : t -> t -> Type} -> Transitive t rel => {x, y : t} -> rel x y -> ForAll (rel y) ys -> ForAll (rel x) ys
proofForAllTransitive _ AllOfEmpty = AllOfEmpty
proofForAllTransitive x_lte_y (AddToAll p_y all_ys) = AddToAll (transitive x_lte_y p_y) (proofForAllTransitive x_lte_y all_ys)

proofForAllAdd : ForAll p xs -> ForAll p ys -> ForAll p (xs ++ ys)
proofForAllAdd AllOfEmpty p_ys = p_ys
proofForAllAdd (AddToAll p_x all_xs) all_ys = AddToAll p_x (proofForAllAdd all_xs all_ys)

proofForAllPerm : ForAll p xs -> Permutation xs ys -> ForAll p ys
proofForAllPerm z SameIsPermutation = z
proofForAllPerm (AddToAll p1 xt) (AddSameHead p2) = AddToAll p1 (proofForAllPerm xt p2)
proofForAllPerm (AddToAll p1 (AddToAll p2 xtt)) SwapFirstTwo = (AddToAll p2 (AddToAll p1 xtt))
proofForAllPerm all_xs (TransitivePerm p1 p2) = proofForAllPerm (proofForAllPerm all_xs p1) p2

proofSingletonIsSorted : {rel : t -> t -> Type} -> Sorted rel [_]
proofSingletonIsSorted = ConsToSorted EmptyIsSorted AllOfEmpty

proofPermSymmetric : Permutation xs ys -> Permutation ys xs
proofPermSymmetric SameIsPermutation      = SameIsPermutation
proofPermSymmetric SwapFirstTwo           = SwapFirstTwo
proofPermSymmetric (AddSameHead p)        = AddSameHead    (proofPermSymmetric p)
proofPermSymmetric (TransitivePerm p1 p2) = TransitivePerm (proofPermSymmetric p2) (proofPermSymmetric p1)

proofPermAddAssociative : {xs, ys, zs : List t} -> Permutation (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
proofPermAddAssociative {xs = []} = SameIsPermutation
proofPermAddAssociative {xs = (x :: xt)} = AddSameHead (proofPermAddAssociative {xs = xt})

proofPermAddCommutative : {xs, ys : List t} -> Permutation (xs ++ ys) (ys ++ xs)
proofPermAddCommutative {xs = []} {ys} = rewrite appendNilRightNeutral ys in SameIsPermutation
proofPermAddCommutative {xs} {ys = []} = rewrite appendNilRightNeutral xs in SameIsPermutation
proofPermAddCommutative {xs = (x :: xt)} {ys = (y :: yt)} =        
        let
        xtyt = proofPermAddCommutative {xs = xt} {ys = yt}
        xsyt = proofPermAddCommutative {xs = (x :: xt)} {ys = yt}
        xtys = proofPermAddCommutative {xs = xt} {ys = (y :: yt)}
        in
        TransitivePerm
                (AddSameHead (TransitivePerm xtys (AddSameHead (proofPermSymmetric xtyt))))
                (TransitivePerm SwapFirstTwo (AddSameHead xsyt))

proofPermAdd_R : {xs, ys, zs : List t} -> Permutation xs ys -> Permutation (xs ++ zs) (ys ++ zs)
proofPermAdd_R SameIsPermutation      = SameIsPermutation
proofPermAdd_R SwapFirstTwo           = SwapFirstTwo
proofPermAdd_R (AddSameHead p)        = AddSameHead    (proofPermAdd_R p)
proofPermAdd_R (TransitivePerm p1 p2) = TransitivePerm (proofPermAdd_R p1) (proofPermAdd_R p2)

proofPermAdd_L : {xs, ys, zs : List t} -> Permutation xs ys -> Permutation (zs ++ xs) (zs ++ ys)
proofPermAdd_L {zs = []} p = p
proofPermAdd_L {zs = (z :: zt)} p = AddSameHead (proofPermAdd_L p)

proofPermAdd : {as, bs, cs, ds : List t} -> Permutation as bs -> Permutation cs ds -> Permutation (as ++ cs) (bs ++ ds)
proofPermAdd pab pcd = TransitivePerm (proofPermAdd_R pab) (proofPermAdd_L pcd)

proofOneToAllTransPerm : {rel : t -> t -> Type} -> Transitive t rel => {x, y : t}
                                                -> ForAll (rel x) xs
                                                -> ForAll (rel y) ys
                                                -> x `rel` y
                                                -> Permutation (xs ++ y :: ys) zs
                                                -> ForAll (rel x) zs
proofOneToAllTransPerm x_lte_xs y_lte_ys x_lte_y p =
        proofForAllPerm (proofForAllAdd x_lte_xs (AddToAll x_lte_y (proofForAllTransitive x_lte_y y_lte_ys))) p

relate : {rel : t -> t -> Type} -> Sortable t rel => (x, y : t) -> Either (rel x y) (rel y x)
relate x y with (decEq x y)
                relate x x | Yes Refl = Left reflexive
                relate x y | No contr = connex contr

mergeTwoLists : {rel : t -> t -> Type} -> Sortable t rel =>
                (xs  : List t) -> Sorted rel xs ->
                (ys  : List t) -> Sorted rel ys ->
                (zs  : List t ** (Sorted rel zs, Permutation (xs ++ ys) zs))
mergeTwoLists [] _ ys ys_sorted = (ys ** (ys_sorted, SameIsPermutation))
mergeTwoLists xs xs_sorted [] _ = rewrite appendNilRightNeutral xs in (xs ** (xs_sorted, SameIsPermutation))
mergeTwoLists (x :: xs) (ConsToSorted xs_sorted p1) (y :: ys) (ConsToSorted ys_sorted p2) = case (relate x y) of
    Left  x_rel_y =>    let
                        (zs ** (zs_sorted, zs_perm)) = (mergeTwoLists xs xs_sorted (y :: ys) (ConsToSorted ys_sorted p2))
                        xzs_sorted = ConsToSorted zs_sorted (proofOneToAllTransPerm p1 p2 x_rel_y zs_perm)
                        in
                        (x :: zs ** (xzs_sorted, AddSameHead zs_perm))
    Right y_rel_x =>    let
                        (zs ** (zs_sorted, zs_perm)) = mergeTwoLists (x :: xs) (ConsToSorted xs_sorted p1) ys ys_sorted
                        yzs_sorted = ConsToSorted zs_sorted (proofOneToAllTransPerm
                                                                p2 p1 y_rel_x (TransitivePerm proofPermAddCommutative zs_perm))
                        yzs_perm = TransitivePerm
                                        (proofPermAddCommutative {xs = (x :: xs)})
                                        (AddSameHead (TransitivePerm proofPermAddCommutative zs_perm))
                        in
                        (y :: zs ** (yzs_sorted, yzs_perm))

concatSingltons : List (s : List t ** Sorted _ s) -> List t
concatSingltons [] = []
concatSingltons ((s ** _) :: st) = s ++ concatSingltons st

mergeSingletons : {rel : t -> t -> Type} -> Sortable t rel =>
                  (ss  : List (s : List t ** Sorted rel s)) ->
                  (xs  : List t ** (Sorted rel xs, Permutation (concatSingltons ss) xs))
mergeSingletons [] = ([] ** (EmptyIsSorted, SameIsPermutation))
mergeSingletons [(s ** s_sorted)] = (s ** (s_sorted, rewrite appendNilRightNeutral s in SameIsPermutation))
mergeSingletons ((sx ** sx_sorted) :: (sy ** sy_sorted) :: st) =
        let
        (merged_st ** (merged_st_sorted, merged_st_perm)) = mergeSingletons st
        (merged_xy ** (merged_xy_sorted, merged_xy_perm)) = mergeTwoLists sx sx_sorted sy sy_sorted
        (xs ** (xs_sorted, xs_perm)) = mergeTwoLists merged_xy merged_xy_sorted merged_st merged_st_sorted
        (final_perm) = TransitivePerm
                            (TransitivePerm
                                (proofPermAddAssociative {xs = sx} {ys = sy} {zs = concatSingltons st})
                                (proofPermAdd merged_xy_perm merged_st_perm))
                            (xs_perm)
        in
        (xs ** (xs_sorted, final_perm))

splitSingletons : {rel : t -> t -> Type} -> Sortable t rel => (xs  : List t) ->
                  (ss  : List (s : List t ** Sorted rel s) ** Permutation xs (concatSingltons ss))
splitSingletons [] = ([] ** SameIsPermutation)
splitSingletons (x :: xt) =     let
                                (tail_ss ** tail_perm) = splitSingletons xt
                                ss : List (s : List t ** Sorted rel s)
                                ss = ([x] ** proofSingletonIsSorted) :: tail_ss
                                perm_xs_ss : Permutation (x :: xt) (concatSingltons ss)
                                perm_xs_ss = TransitivePerm (AddSameHead tail_perm) SameIsPermutation
                                in
                                (ss ** perm_xs_ss)

mergeSort : {rel : t -> t -> Type} -> Sortable t rel => (xs  : List t) -> (ys  : List t ** (Sorted rel ys, Permutation xs ys))
mergeSort xs =  let
                (ss ** split_perm) = splitSingletons xs
                (ys ** (ys_sorted, merge_perm)) = mergeSingletons ss
                in
                (ys ** (ys_sorted, TransitivePerm split_perm merge_perm))

Sortable Nat LTE where

main : IO ()
main = do
        putStrLn (show (fst (mergeSort {rel = LTE} my_list_nat)));

        where
                my_list_nat : List Nat
                my_list_nat = [5, 0, 1, 3, 2, 4]