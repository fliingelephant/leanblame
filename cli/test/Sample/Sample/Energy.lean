import Sample.Basic

namespace Sample

/-- The energy of a point: the energy of a chain as long as the point's norm. -/
@[trusted] def pointEnergy (p : Point) : Nat := energy p.norm

/-- The second site of a three-site chain is site number two. The statement contains a proof
(that `2 < 3`); `test/run.sh` swaps it for another one. -/
@[trusted] theorem second_site : (⟨2, by decide⟩ : Fin 3).val = 2 := rfl

/-- The energy of every chain is even. Open: the proof is `sorry`. -/
@[trusted] theorem energy_even (n : Nat) : energy n % 2 = 0 := by
  sorry

end Sample
