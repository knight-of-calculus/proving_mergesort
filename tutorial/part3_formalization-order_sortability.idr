import Decidable.Equality
import Control.Order

%default total

-- 5. формализуем понятия порядка и сортируемости
interface (DecEq t, LinearOrder t rel) => Sortable t rel where

-- пример собственной реализации
interface Relation_Reflexive      t rel | rel where reflexive     : {x       : t} -> rel x x
interface Relation_Transitive     t rel | rel where transitive    : {x, y, z : t} -> rel x y -> rel y z -> rel x z
interface Relation_Antisymmetric  t rel | rel where antisymmetric : {x, y    : t} -> rel x y -> rel y x -> x = y
interface Relation_Connex         t rel | rel where connex        : {x, y    : t} -> Not (x = y) -> Either (rel x y) (rel y x)

interface (Relation_Reflexive     t rel,
           Relation_Transitive    t rel,
           Relation_Antisymmetric t rel,
           Relation_Connex        t rel) => LinOrder t rel where -- StronglyConnex для TotalOrder