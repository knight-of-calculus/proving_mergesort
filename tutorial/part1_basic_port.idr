%default total

mergeTwoLists : List Int -> List Int -> List Int
mergeTwoLists [] ys = ys
mergeTwoLists xs [] = xs
mergeTwoLists xs@(x :: xt) ys@(y :: yt) with (compare x y)
    _ | LT = x :: mergeTwoLists xt ys
    _ | EQ = x :: mergeTwoLists xt ys
    _ | GT = y :: mergeTwoLists xs yt

mergeSingletons : List (List Int) -> List Int
mergeSingletons [] = []
mergeSingletons [s] = s
mergeSingletons (sx :: sy :: st) = mergeTwoLists (mergeTwoLists sx sy) (mergeSingletons st)

splitSingletons : List Int -> List (List Int)
splitSingletons [] = []
splitSingletons (x :: xt) = [x] :: (splitSingletons xt)

mergeSort : List Int -> List Int
mergeSort xs = (mergeSingletons . splitSingletons) xs

main : IO ()
main = do
        putStrLn ("input:\t"  ++ (show my_list));
        putStrLn ("sorted:\t" ++ (show (mergeSort my_list)));
        where my_list : List Int
              my_list = [5, 1, 3, 2, 4]

-- чем это лучше Python?
--      сэкономили ~ 10 строк кода :), но при этом:
--      нет ограничения на глубину рекурсии, встроенные оптимизации для такого подхода;
--      рекурсия и структурное сопоставление с образцом -- "родная среда" ФП;
--      гарантированная тотальность:
--              все функции определены для всех возможных значений входных параметров,
--              все функции завершаются на всех входах (т.е. мы точно не уйдем в бесконечные циклы).
-- однако, такой код все же не является гарантированно корректным... пока :)