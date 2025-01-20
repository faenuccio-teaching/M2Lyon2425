import Init.Data.List.Basic
import Mathlib.Data.PNat.Basic



inductive Stations : Type*
  | PartDieu : Stations
  | Perrache : Stations

structure Line where
  stops : List Stations
  not_empty : stops ≠ []
  nodup : stops.Nodup

structure Trip where
  n : ℕ+ -- the number of stops
  select : Fin n → Stations
  inj : select.Injective


-- -- #check Line.notempty
-- def Start (L : Line) : Stations := by
--   exact (L.stops).head (L.not_empty)

-- def End (L : Line) : Stations := by
--   exact (L.stops).length-- (L.not_empty)

-- inductive Terminus (L : Line) : Type*
--   | Start M : Terminus L
--   -- | (stops L).head (not_empty L) : Terminus
