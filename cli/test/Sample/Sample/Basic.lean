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

/-- Two is positive. Nothing tagged uses it, so a challenge leaves it out; `test/run.sh` makes a
tagged definition use it, through `two`, and then the challenge holds its proof. -/
theorem two_pos : 0 < 2 := by decide

/-- Two, as a positive number. -/
def two : {n : Nat // 0 < n} := ⟨2, two_pos⟩

end Sample
