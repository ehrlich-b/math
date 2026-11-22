import PaperA.SpinFieldV4

noncomputable section
namespace PaperA

abbrev Spin (d : ℕ) := ℝ × Vec d
def spinMul {d : ℕ} (a b : Spin d) : Spin d :=
  (a.1 * b.1 + inner ℝ a.2 b.2, a.1 • b.2 + b.1 • a.2)
def spinUnit (d : ℕ) : Spin d := (1, 0)
def spinAtom {d : ℕ} (v : Vec d) : Spin d := ((1 / 2 : ℝ), (1 / 2 : ℝ) • v)

end PaperA
