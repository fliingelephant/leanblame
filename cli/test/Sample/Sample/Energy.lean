import Sample.Basic

namespace Sample

/-- The energy of a point: the energy of a chain as long as the point's norm. -/
@[trusted] def pointEnergy (p : Point) : Nat := energy p.norm

/-- The energy of every chain is even. Open: the proof is `sorry`. -/
@[trusted] theorem energy_even (n : Nat) : energy n % 2 = 0 := by
  sorry

end Sample
