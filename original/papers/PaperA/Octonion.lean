import Mathlib.Analysis.Quaternion

noncomputable section
namespace PaperA

abbrev Oct := Quaternion ℝ × Quaternion ℝ
def octConj (x : Oct) : Oct := (star x.1, -x.2)
def octMul (x y : Oct) : Oct := (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

end PaperA
