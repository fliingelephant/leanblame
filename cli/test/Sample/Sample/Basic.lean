import LeanBlame.Attr

namespace Sample

/-- Twice a natural number. -/
def double (n : Nat) : Nat := n + n

/-- The energy of a chain of `n` sites: two units per site. -/
@[trusted] def energy (n : Nat) : Nat := double n

/-- A point in the plane with natural-number coordinates. -/
@[trusted] structure Point where
  /-- The horizontal coordinate. -/
  x : Nat
  /-- The vertical coordinate. -/
  y : Nat

/-- The taxicab norm of a point: the sum of its two coordinates. -/
@[trusted] def Point.norm (p : Point) : Nat := p.x + p.y

end Sample
