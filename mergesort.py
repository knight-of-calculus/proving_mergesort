from typing import List
from random import randint

def mergeTwoLists(xs: List[int], ys: List[int]) -> List[int]:
    if len(xs) == 0: return ys
    if len(ys) == 0: return xs

    x, *xt = xs
    y, *yt = ys

    if x <= y: return [x] + mergeTwoLists(xt, ys)

    return [y] + mergeTwoLists(xs, yt)

def mergeSingletons(ss: List[List[int]]) -> List[int]:
    if len(ss) == 0: return []
    if len(ss) == 1: return ss[0]

    sx, sy, *st = ss

    return mergeTwoLists(mergeTwoLists(sx, sy), mergeSingletons(st))

def splitSingletons(xs: List[int]) -> List[List[int]]:
    return list(map(lambda x: [x], xs))

def mergeSort(xs: List[int]) -> List[int]:
    return mergeSingletons(splitSingletons(xs))

if __name__ == '__main__':
    my_list : List[int] = list(map(lambda _: randint(-100, 100), range(randint(0, 1000))))  # максимальная глубина рекурсии
    result  : List[int] = mergeSort(my_list)                                                # в Python = 1000, т.е. мы можем подать
                                                                                            # на вход список длины максимум ~1k эл.;
    # можно обойти это ограничение, если сделать рекурсивные вызовы хвостовыми и применить самописную оптимизацию хвостовой рекурсии
    assert result == sorted(my_list), 'result is wrong'

    print('input:',  my_list, sep = '\t')
    print('sorted:', result,  sep = '\t')