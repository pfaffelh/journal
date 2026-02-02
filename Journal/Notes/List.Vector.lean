import Mathlib


instance traversable_list : Traversable (List) := by exact instTraversableList

#check List.traverse
-- #check List.Vector.mk

example (v : List.Vector α n) : v.val.length = n := by exact List.Vector.length_val v


namespace List.Vector

instance : Traversable.{u} (Vector · n) where
  traverse := @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

example (n : ℕ) : (flip Vector n) = (Vector · n) := rfl

instance : LawfulTraversable.{u} (Vector · n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl

end List.Vector
