import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F0
import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F1
import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F2
import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F3
import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F4
import IdealArithmetic.Examples.NF3_1_981215_1.PrimesBelow3_1_981215_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 280]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 281 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB281I0
  exact PB281I1
  exact PB281I2
  exact PB281I3
  exact PB281I4
  exact PB281I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB281 : PrimesBelowBoundCertificate O 281 := by
  refine primesBelowBoundCertificate_of_Interval O eC 280 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 280 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 280 hC

lemma cert_eq_𝔭 : PB281.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 280 rfl rfl hel hC
