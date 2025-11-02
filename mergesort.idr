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

{- или так:
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
-}

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

-- отношения для индуктивных типов (Nat)

Reflexive     Nat GTE where reflexive                     = reflexive     {rel = LTE}
Transitive    Nat GTE where transitive    x_gte_y y_gte_z = transitive    {rel = LTE} y_gte_z x_gte_y
Antisymmetric Nat GTE where antisymmetric x_gte_y y_gte_x = antisymmetric {rel = LTE} y_gte_x x_gte_y
Connex        Nat GTE where connex        x_neq_y         = case connex   {rel = LTE} x_neq_y of
                                                                Left  x_lte_y => Right x_lte_y
                                                                Right y_lte_x => Left  y_lte_x

Preorder     Nat GTE where
PartialOrder Nat GTE where
LinearOrder  Nat GTE where

Sortable     Nat LTE where
Sortable     Nat GTE where

-- отношения для примитивных типов (Int, String, etc; условие: интерфейс Ord)

data CompareLTE : (x, y : t) -> Type where
        Cmp_LTE : CompareLTE x y

data CompareGTE : (x, y : t) -> Type where
        Cmp_GTE : CompareGTE x y

interface Ord t => Ordered t where
        relateCmp : (x, y : t) -> Either (CompareLTE x y) (CompareGTE x y)

Ord t => Ordered t where
        relateCmp x y = case compare x y of
                        LT => Left  Cmp_LTE
                        EQ => Left  Cmp_LTE
                        GT => Right Cmp_GTE

Ordered t => Reflexive  t (CompareLTE {t}) where reflexive = Cmp_LTE
Ordered t => Reflexive  t (CompareGTE {t}) where reflexive = Cmp_GTE

Ordered t => Transitive t (CompareLTE {t}) where transitive Cmp_LTE Cmp_LTE = Cmp_LTE
Ordered t => Transitive t (CompareGTE {t}) where transitive Cmp_GTE Cmp_GTE = Cmp_GTE

Ordered t => Antisymmetric t (CompareLTE {t}) where
        antisymmetric Cmp_LTE Cmp_LTE = believe_me () -- ?H1

Ordered t => Antisymmetric t (CompareGTE {t}) where
        antisymmetric Cmp_GTE Cmp_GTE = believe_me () -- ?H2

Ordered t => Connex t (CompareLTE {t}) where
        connex x_neq_y = case (relateCmp x y) of
                                Left  l => Left l
                                Right r => case (relateCmp y x) of
                                                Left  l' => Right  l'
                                                Right r' => absurd (x_neq_y (antisymmetric r r'))

Ordered t => Connex t (CompareGTE {t}) where
        connex x_neq_y = case (relateCmp x y) of
                                Right r => Left r
                                Left  l => case (relateCmp y x) of
                                                Right r' => Right r'
                                                Left  l' => absurd (x_neq_y (antisymmetric l l'))

Ord t => Preorder     t CompareLTE where
Ord t => PartialOrder t CompareLTE where
Ord t => LinearOrder  t CompareLTE where
Ord t => Preorder     t CompareGTE where
Ord t => PartialOrder t CompareGTE where
Ord t => LinearOrder  t CompareGTE where

(DecEq t, Ord t) => Sortable t CompareLTE where
(DecEq t, Ord t) => Sortable t CompareGTE where

main : IO ()
main = do
        putStrLn (show (fst (mergeSort {rel = LTE} my_list_nat)));
        putStrLn (show (fst (mergeSort {rel = GTE} my_list_nat)));

        putStrLn (show (fst (mergeSort {rel = CompareLTE} my_list_int)));
        putStrLn (show (fst (mergeSort {rel = CompareGTE} my_list_int)));

        putStrLn (show (fst (mergeSort {rel = CompareLTE} my_list_str)));
        putStrLn (show (fst (mergeSort {rel = CompareGTE} my_list_str)));

        putStrLn (show (fst (mergeSort {rel = CompareLTE} my_list_chr)));
        putStrLn (show (fst (mergeSort {rel = CompareGTE} my_list_chr)));

        where
                my_list_nat : List Nat
                my_list_nat = [5, 1, 3, 0, 2, 4]

                x = Num
                my_list_int : List Int
                my_list_int = [5, -5, -1, 3, 1, 0, 2, -2, -4, 4, -3]

                my_list_str : List String
                my_list_str = ["ace", "edba", "abcde", "ecad", "abec"]

                my_list_chr : List Char
                my_list_chr = ['а', '4', 'о', 'z', 'ы', '1', 'a', 'н', 'r']