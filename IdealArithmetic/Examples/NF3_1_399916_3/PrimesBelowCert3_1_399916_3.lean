import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F0
import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F1
import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F2
import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 178]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 179 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB179I0
  exact PB179I1
  exact PB179I2
  exact PB179I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB179 : PrimesBelowBoundCertificate O 179 := by
  refine primesBelowBoundCertificate_of_Interval O eC 178 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 178 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 178 hC

lemma cert_eq_𝔭 : PB179.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 178 rfl rfl hel hC
