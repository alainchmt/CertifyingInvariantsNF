import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F0
import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F1
import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F2
import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F3
import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 208]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 209 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB209I0
  exact PB209I1
  exact PB209I2
  exact PB209I3
  exact PB209I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB209 : PrimesBelowBoundCertificate O 209 := by
  refine primesBelowBoundCertificate_of_Interval O eC 208 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 208 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 208 hC

lemma cert_eq_𝔭 : PB209.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 208 rfl rfl hel hC
