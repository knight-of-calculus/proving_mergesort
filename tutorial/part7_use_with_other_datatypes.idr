import Data.Nat
import Decidable.Equality
import Control.WellFounded

%default total

interface (DecEq t, LinearOrder t rel) => Sortable t rel where

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

-- поскольку примитивные типы не имеют строгой семантики, мы не всегда можем рассуждать об их свойствах
-- например, мы понимаем, что при корректной реализации сравнений в примитивах наши компараторы удовлетворяют антисимметричности,
-- но как это формально доказать?
Ordered t => Antisymmetric t (CompareLTE {t}) where
        antisymmetric Cmp_LTE Cmp_LTE = believe_me () -- ?H1

Ordered t => Antisymmetric t (CompareGTE {t}) where
        antisymmetric Cmp_GTE Cmp_GTE = believe_me () -- ?H2
-- решение 1:   переписать примитивные типы на индуктивные, чтобы их структура была доступна в рамках нашего языка
-- решение 2:   использовать технику наделения определенных операций (булевы сравнения, которые будут происходить в runtime)
--              явной семантикой, с помощью оборачивания So : Bool -> Type

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