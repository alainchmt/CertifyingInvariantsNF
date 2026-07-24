import IdealArithmetic.Examples.NF3_1_112887_1.PrimesBelow3_1_112887_1F0
import IdealArithmetic.Examples.NF3_1_112887_1.PrimesBelow3_1_112887_1F1
import IdealArithmetic.Examples.NF3_1_112887_1.PrimesBelow3_1_112887_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 95]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 96 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB96I0
  exact PB96I1
  exact PB96I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB96 : PrimesBelowBoundCertificate O 96 := by
  refine primesBelowBoundCertificate_of_Interval O eC 95 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 95 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 95 hC

lemma cert_eq_𝔭 : PB96.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 95 rfl rfl hel hC
