import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F0
import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F1
import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F2
import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 166]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 167 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB167I0
  exact PB167I1
  exact PB167I2
  exact PB167I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB167 : PrimesBelowBoundCertificate O 167 := by
  refine primesBelowBoundCertificate_of_Interval O eC 166 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 166 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 166 hC

lemma cert_eq_𝔭 : PB167.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 166 rfl rfl hel hC
